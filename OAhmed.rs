use sha2::{Digest, Sha256};
use std::fmt::Debug;
static mut INSTANCE_COUNT: usize = 0;
pub trait SumCommitment {
    fn amount(&self) -> u64;
    fn digest(&self) -> [u8; 32];
    fn height(&self) -> u8;
}

pub trait ExclusiveAllotmentProof<C: SumCommitment + Clone + Debug> {
    fn position(&self) -> usize;
    fn sibling(&self, height: u8, my_nodes: &[C]) -> Option<Self>
    where
        Self: Sized;
    fn verify(&self, root_commitment: &C) -> bool;
}

pub trait MerkleTree<C, P> {
    fn new(values: Vec<C>) -> Self;
    fn commit(&self) -> C;
    fn prove(&self, position: usize) -> P
    where
        Self: Sized;
    fn calculate(&mut self);
}

#[derive(Clone, Debug)]
pub struct MySumCommitment {
    amount: u64,
    digest: [u8; 32],
    height: u8,
}

impl MySumCommitment {
    pub fn new(amount: u64, height: u8) -> Self {
        let digest = hash_bytes(&amount.to_be_bytes());
        MySumCommitment {
            amount,
            digest,
            height,
        }
    }
}

impl SumCommitment for MySumCommitment {
    fn amount(&self) -> u64 {
        self.amount
    }

    fn digest(&self) -> [u8; 32] {
        self.digest
    }

    fn height(&self) -> u8 {
        self.height
    }
}
pub struct MyExclusiveAllotmentProof<C: SumCommitment> {
    position: usize,
    sibling: Option<C>,
}
impl<C: SumCommitment> MyExclusiveAllotmentProof<C> {
    pub fn new(position: usize, sibling: Option<C>) -> Self {
        MyExclusiveAllotmentProof { position, sibling }
    }
}
impl<C: SumCommitment + Clone + Debug> ExclusiveAllotmentProof<C> for MyExclusiveAllotmentProof<C> {
    fn position(&self) -> usize {
        self.position
    }
    fn sibling(&self, height: u8, my_nodes: &[C]) -> Option<Self> {
        let sibling_position = if self.position % 2 == 0 {
            self.position + 1
        } else {
            self.position - 1
        };
        let sibling_height = self.sibling.as_ref().map(|s| s.height()).unwrap_or(0);

        if sibling_height != height {
            return None;
        }
        let count = my_nodes
            .iter()
            .filter(|node| node.height() == height)
            .count();
        if sibling_position + 2 == count {
            for node in my_nodes {
                if node.height() == height {
                    return Some(MyExclusiveAllotmentProof::new(
                        sibling_position,
                        Some(node.clone()),
                    ));
                }
            }
        }

        Some(MyExclusiveAllotmentProof::new(
            sibling_position,
            self.sibling.clone(),
        ))
    }
    fn verify(&self, root_commitment: &C) -> bool {
        self.sibling.clone().unwrap().digest() == root_commitment.digest()
            && self.sibling.clone().unwrap().amount() == root_commitment.amount()
    }
}

pub struct MyMerkleTree {
    values: Vec<MySumCommitment>,
    my_nodes: Vec<MySumCommitment>,
}
impl MerkleTree<MySumCommitment, MyExclusiveAllotmentProof<MySumCommitment>> for MyMerkleTree {
    fn new(values: Vec<MySumCommitment>) -> Self {
        let mut tree = MyMerkleTree {
            values,
            my_nodes: Vec::new(),
        };
        tree.calculate();
        tree
    }
    fn commit(&self) -> MySumCommitment {
        let mut nodes = self.values.iter().map(|v| v.clone()).collect::<Vec<_>>();
        let mut height = 1;
        let mut Nodes1;
        let mut my_nodes: Vec<MySumCommitment> =
            self.values.iter().map(|v| v.clone()).collect::<Vec<_>>();
        while nodes.len() > 1 {
            Nodes1 = Vec::new();
            for chunk in nodes.chunks(2) {
                let left = chunk[0].clone();
                let right = if chunk.len() > 1 {
                    chunk[1].clone()
                } else {
                    left.clone()
                };
                let mut buf = [0u8; 64];
                buf[..32].copy_from_slice(&left.digest());
                buf[32..].copy_from_slice(&right.digest());
                let hash = hash_bytes(&buf);
                let t_amount = left.amount() + right.amount();
                let new_node = MySumCommitment {
                    amount: t_amount,
                    digest: hash,
                    height,
                };
                if height > 0 {
                    my_nodes.push(new_node.clone());
                }
                Nodes1.push(new_node);
            }
            height += 1;
            nodes = Nodes1.clone();
        }
        nodes.pop().unwrap()
    }

    fn prove(&self, position: usize) -> MyExclusiveAllotmentProof<MySumCommitment> {
        let mut idx = position; // 0
        let Nodes2 = self.my_nodes.clone();

        let mut proofs = Vec::new();
        let mut cur_height = 0;

        let root_node = Nodes2.iter().max_by_key(|node| node.height()).unwrap();
        let root_height = root_node.height();

        let current_node = getNode(&Nodes2, idx, cur_height).unwrap();

        proofs.push(MyExclusiveAllotmentProof::new(
            idx,
            Some(current_node.clone()),
        ));

        while cur_height < root_height {
            let sibling_idx = if idx % 2 == 0 { idx + 1 } else { idx - 1 };

            let sibling_node = getNode(&Nodes2, sibling_idx, cur_height).unwrap();

            let level_proof =
                MyExclusiveAllotmentProof::new(idx, Some(sibling_node.clone().into()));
            proofs.push(level_proof);

            idx = sibling_idx / 2;
            cur_height += 1;
        }
        let mut hashes = Vec::new();
        for node in Nodes2.iter() {
            hashes.push(node.digest());
        }
        let hashes: Vec<Vec<u8>> = Nodes2.iter().map(|node| node.digest().to_vec()).collect();

        let mut result = proofs[0].sibling.clone();
        for i in 1..proofs.len() {
            let combined = match (result, proofs[i].sibling.clone()) {
                (Some(left), Some(right)) => {
                    let mut buf = [0u8; 64];

                    let position = LeftOrRight(left.digest(), &hashes);

                    if position % 2 == 0 {
                        buf[..32].copy_from_slice(&left.digest());
                        buf[32..].copy_from_slice(&right.digest());
                    } else {
                        buf[..32].copy_from_slice(&right.digest());
                        buf[32..].copy_from_slice(&left.digest());
                    }
                    let hash = hash_bytes(&buf);

                    Some(MySumCommitment {
                        amount: left.amount() + right.amount(),
                        digest: hash,
                        height: left.height(),
                    })
                }
                _ => None,
            };
            result = combined;
        }
        MyExclusiveAllotmentProof::new(idx, result)
    }
    fn calculate(&mut self) {
        let mut nodes = self.values.iter().map(|v| v.clone()).collect::<Vec<_>>();
        let mut height = 1;
        let mut Nodes1;
        let mut my_nodes: Vec<MySumCommitment> =
            self.values.iter().map(|v| v.clone()).collect::<Vec<_>>();
        while nodes.len() > 1 {
            Nodes1 = Vec::new();
            for chunk in nodes.chunks(2) {
                let left = chunk[0].clone();
                let right = if chunk.len() > 1 {
                    chunk[1].clone()
                } else {
                    left.clone()
                };
                let mut buf = [0u8; 64];
                buf[..32].copy_from_slice(&left.digest());
                buf[32..].copy_from_slice(&right.digest());
                let hash = hash_bytes(&buf);
                let t_amount = left.amount() + right.amount();
                let new_node = MySumCommitment {
                    amount: t_amount,
                    digest: hash,
                    height,
                };
                if height > 0 {
                    my_nodes.push(new_node.clone());
                }
                Nodes1.push(new_node);
            }
            height += 1;
            nodes = Nodes1.clone();
        }
        self.my_nodes = my_nodes;
    }
}
fn LeftOrRight(hash: [u8; 32], hashes: &[Vec<u8>]) -> usize {
    let mut count = 0;
    for Hash1 in hashes {
        if Hash1 == &hash {
            return count;
        }
        count += 1;
    }
    0
}

fn hash_bytes(slice: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(slice);
    hasher.finalize().into()
}
fn getNode<C: SumCommitment>(my_nodes: &[C], position: usize, height: u8) -> Option<&C> {
    let mut count = 0;
    for node in my_nodes {
        if node.height() == height {
            if count == position {
                return Some(node);
            }
            count += 1;
        }
    }
    None
}
fn main() {
    let values = vec![
        MySumCommitment::new(10, 0),
        MySumCommitment::new(15, 0),
        MySumCommitment::new(35, 0),
        MySumCommitment::new(50, 0),
    ];

    let tree = MyMerkleTree::new(values);
    let commit = tree.commit();
    let proof = tree.prove(3);
    println!("proof: {:?}", proof.sibling);

    let verified = proof.verify(&commit);
    println!("verified: {:?}", verified);
}
