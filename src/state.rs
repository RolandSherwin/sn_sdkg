// Copyright 2022 MaidSafe.net limited.
//
// This SAFE Network Software is licensed to you under The General Public License (GPL), version 3.
// Unless required by applicable law or agreed to in writing, the SAFE Network Software distributed
// under the GPL Licence is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
// KIND, either express or implied. Please review the Licences for the specific language governing
// permissions and limitations relating to use of the SAFE Network Software.

use bls::{PublicKey, PublicKeySet, SecretKey, SecretKeyShare, Signature};
use std::collections::{BTreeMap, BTreeSet};

use crate::error::{Error, Result};
use crate::knowledge::{Knowledge, KnowledgeFault};
use crate::sdkg::{AckOutcome, Part, PartOutcome, SyncKeyGen};
use crate::vote::{DkgSignedVote, DkgVote, IdAck, IdPart, NodeId};

/// State of the Dkg session, contains the sync keygen and currently known Parts and Acks
/// Can handle votes coming from other participants
pub struct DkgState {
    id: NodeId,
    secret_key: SecretKey,
    pub_keys: BTreeMap<NodeId, PublicKey>,
    keygen: SyncKeyGen<NodeId>,
    our_part: Part,
    all_votes: BTreeSet<DkgSignedVote>,
}

/// State after handling a vote
pub enum VoteResponse {
    /// We need more votes to decide on anything yet
    WaitingForMoreVotes,
    /// This vote has already been processed
    IgnoringKnownVote,
    /// Broadcast our vote to the other participants
    BroadcastVote(Box<DkgSignedVote>),
    /// We are missing information to understand this vote
    RequestAntiEntropy,
    /// DKG is completed on our side
    DkgComplete(PublicKeySet, SecretKeyShare),
}

enum DkgCurrentState {
    IncompatibleVotes,
    NeedAntiEntropy,
    Termination(BTreeMap<IdPart, BTreeSet<IdAck>>),
    WaitingForTotalAgreement(BTreeMap<IdPart, BTreeSet<IdAck>>),
    GotAllAcks(BTreeMap<IdPart, BTreeSet<IdAck>>),
    WaitingForMoreAcks(BTreeSet<IdPart>),
    GotAllParts(BTreeSet<IdPart>),
    WaitingForMoreParts,
}

impl DkgState {
    /// Creates a new DkgState for a new DKG session with all the participants in `pub_keys`
    /// Each participant needs to have a unique NodeId and a unique public key
    /// The threshold is the desired threshold for the generated bls key set
    pub fn new<R: bls::rand::RngCore>(
        our_id: NodeId,
        secret_key: SecretKey,
        pub_keys: BTreeMap<NodeId, PublicKey>,
        threshold: usize,
        mut rng: R,
    ) -> Result<Self> {
        let (sync_key_gen, opt_part) = SyncKeyGen::new(
            our_id,
            secret_key.clone(),
            pub_keys.clone(),
            threshold,
            &mut rng,
        )?;
        Ok(DkgState {
            id: our_id,
            secret_key,
            pub_keys,
            keygen: sync_key_gen,
            all_votes: BTreeSet::new(),
            our_part: opt_part.ok_or(Error::NotInPubKeySet)?,
        })
    }

    /// Our own NodeId
    pub fn id(&self) -> NodeId {
        self.id
    }

    /// The 1st vote with our Part
    pub fn first_vote(&mut self) -> Result<DkgSignedVote> {
        let vote = DkgVote::SinglePart(self.our_part.clone());
        self.cast_vote(vote)
    }

    fn get_validated_vote(&self, vote: &DkgSignedVote) -> Result<DkgVote> {
        let sender_id = vote.voter;
        let sender_pub_key = self.pub_keys.get(&sender_id).ok_or(Error::UnknownSender)?;
        let vote = vote.get_validated_vote(sender_pub_key)?;
        Ok(vote)
    }

    fn all_checked_votes(&self) -> Result<Vec<(DkgVote, NodeId)>> {
        self.all_votes
            .iter()
            .map(|v| Ok((self.get_validated_vote(v)?, v.voter)))
            .collect()
    }

    fn current_dkg_state(&self, votes: Vec<(DkgVote, NodeId)>) -> DkgCurrentState {
        let knowledge = match Knowledge::from_votes(votes) {
            Err(KnowledgeFault::IncompatibleAcks) | Err(KnowledgeFault::IncompatibleParts) => {
                return DkgCurrentState::IncompatibleVotes;
            }
            Err(KnowledgeFault::MissingParts) | Err(KnowledgeFault::MissingAcks) => {
                return DkgCurrentState::NeedAntiEntropy;
            }
            Ok(k) => k,
        };

        let num_participants = self.pub_keys.len();
        if knowledge.agreed_with_all_acks.len() == num_participants {
            DkgCurrentState::Termination(knowledge.part_acks)
        } else if !knowledge.agreed_with_all_acks.is_empty() {
            DkgCurrentState::WaitingForTotalAgreement(knowledge.part_acks)
        } else if knowledge.got_all_acks(num_participants) {
            DkgCurrentState::GotAllAcks(knowledge.part_acks)
        } else if !knowledge.part_acks.is_empty() {
            DkgCurrentState::WaitingForMoreAcks(knowledge.parts)
        } else if knowledge.parts.len() == num_participants {
            DkgCurrentState::GotAllParts(knowledge.parts)
        } else {
            DkgCurrentState::WaitingForMoreParts
        }
    }

    // Current DKG state taking last vote's type into account
    fn dkg_state_with_vote(
        &self,
        votes: Vec<(DkgVote, NodeId)>,
        vote: &DkgVote,
        is_new: bool,
    ) -> DkgCurrentState {
        let dkg_state = self.current_dkg_state(votes);
        match dkg_state {
            // This case happens when we receive the last Part but we already received
            // someone's acks before, making us skip GotAllParts as we already have an Ack
            DkgCurrentState::WaitingForMoreAcks(parts)
                if is_new && matches!(vote, DkgVote::SinglePart(_)) =>
            {
                DkgCurrentState::GotAllParts(parts)
            }
            // Similarly this happens when we receive the last Ack but we already received
            // someone's agreement on all acks before, making us skip GotAllAcks
            DkgCurrentState::WaitingForTotalAgreement(part_acks)
                if is_new && matches!(vote, DkgVote::SingleAck(_)) =>
            {
                DkgCurrentState::GotAllAcks(part_acks)
            }
            _ => dkg_state,
        }
    }

    pub fn sign_vote(&self, vote: &DkgVote) -> Result<Signature> {
        let sig = self.secret_key.sign(&bincode::serialize(vote)?);
        Ok(sig)
    }

    /// Sign, log and return the vote
    fn cast_vote(&mut self, vote: DkgVote) -> Result<DkgSignedVote> {
        let sig = self.sign_vote(&vote)?;
        let signed_vote = DkgSignedVote::new(vote, self.id, sig);
        self.all_votes.insert(signed_vote.clone());
        Ok(signed_vote)
    }

    /// Handles all the Acks
    fn handle_all_acks(&mut self, all_acks: BTreeMap<IdPart, BTreeSet<IdAck>>) -> Result<()> {
        for ((part_id, _part), acks) in all_acks {
            for (sender_id, ack) in acks {
                let outcome = self.keygen.handle_ack(&sender_id, ack.clone())?;
                if let AckOutcome::Invalid(fault) = outcome {
                    return Err(Error::FaultyVote(format!(
                        "Ack fault: {fault:?} by {sender_id:?} for part by {part_id:?}"
                    )));
                }
            }
        }
        Ok(())
    }

    /// Handles the Parts to create the Acks
    fn parts_into_acks<R: bls::rand::RngCore>(
        &mut self,
        parts: BTreeSet<IdPart>,
        mut rng: R,
    ) -> Result<DkgVote> {
        let mut acks = BTreeMap::new();
        for (sender_id, part) in parts {
            match self
                .keygen
                .handle_part(&sender_id, part.clone(), &mut rng)?
            {
                PartOutcome::Valid(Some(ack)) => {
                    acks.insert((sender_id, part), ack);
                }
                PartOutcome::Invalid(fault) => {
                    return Err(Error::FaultyVote(format!(
                        "Part fault: {fault:?} by {sender_id:?}"
                    )));
                }
                PartOutcome::Valid(None) => {
                    // code smell: we don't have observer nodes and we can't end up here if we've
                    // handled parts and given our acks already, this should not happen unless our
                    // votes were corrupted
                    return Err(Error::FaultyVote("unexpected part outcome, node is faulty or keygen already handled this part".to_string()));
                }
            }
        }
        Ok(DkgVote::SingleAck(acks))
    }

    /// Returns all the votes that we received
    pub fn all_votes(&self) -> Vec<DkgSignedVote> {
        self.all_votes.iter().cloned().collect()
    }

    /// After termination, returns Some keypair else returns None
    /// This function assumes that the Acks have been processed before hand
    /// when receiving the final ack vote
    pub fn outcome(&self) -> Result<Option<(PublicKeySet, SecretKeyShare)>> {
        let votes = self.all_checked_votes()?;
        if let DkgCurrentState::Termination(_) = self.current_dkg_state(votes) {
            if let (pubs, Some(sec)) = self.keygen.generate()? {
                Ok(Some((pubs, sec)))
            } else {
                Ok(None)
            }
        } else {
            Ok(None)
        }
    }

    /// Checks if we reached termination
    pub fn reached_termination(&self) -> Result<bool> {
        let votes = self.all_checked_votes()?;
        let state = self.current_dkg_state(votes);
        Ok(matches!(state, DkgCurrentState::Termination(_)))
    }

    /// Handle a DKG vote, save the information if we learned any, broadcast:
    /// - SingleAck when got all parts
    /// - AllAcks when got all acks
    /// Consider we reached completion when we received everyone's signatures over the AllAcks
    pub fn handle_signed_vote<R: bls::rand::RngCore>(
        &mut self,
        msg: DkgSignedVote,
        rng: R,
    ) -> Result<VoteResponse> {
        // if already seen it, ignore it
        if self.all_votes.contains(&msg) {
            return Ok(VoteResponse::IgnoringKnownVote);
        }

        // immediately bail if signature check fails
        let last_vote = self.get_validated_vote(&msg)?;

        // update knowledge with vote
        let is_new_vote = self.all_votes.insert(msg);
        let votes = self.all_checked_votes()?;
        let dkg_state = self.dkg_state_with_vote(votes, &last_vote, is_new_vote);

        // act accordingly
        match dkg_state {
            DkgCurrentState::NeedAntiEntropy => Ok(VoteResponse::RequestAntiEntropy),
            DkgCurrentState::Termination(acks) => {
                self.handle_all_acks(acks)?;
                if let (pubs, Some(sec)) = self.keygen.generate()? {
                    Ok(VoteResponse::DkgComplete(pubs, sec))
                } else {
                    Err(Error::FailedToGenerateSecretKeyShare)
                }
            }
            DkgCurrentState::GotAllAcks(acks) => {
                let vote = DkgVote::AllAcks(acks);
                Ok(VoteResponse::BroadcastVote(Box::new(self.cast_vote(vote)?)))
            }
            DkgCurrentState::GotAllParts(parts) => {
                let vote = self.parts_into_acks(parts, rng)?;
                Ok(VoteResponse::BroadcastVote(Box::new(self.cast_vote(vote)?)))
            }
            DkgCurrentState::WaitingForMoreParts
            | DkgCurrentState::WaitingForMoreAcks(_)
            | DkgCurrentState::WaitingForTotalAgreement(_) => Ok(VoteResponse::WaitingForMoreVotes),
            DkgCurrentState::IncompatibleVotes => {
                Err(Error::FaultyVote("got incompatible votes".to_string()))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bls::rand::{rngs::StdRng, seq::IteratorRandom, thread_rng, SeedableRng};
    use proptest::prelude::*;

    #[test]
    fn gg() -> Result<()> {
        let num_nodes = 7;
        let threshold = 4;
        let seed = 123;
        let mut rng = StdRng::seed_from_u64(seed);

        let mut nodes = generate_nodes(num_nodes, threshold, &mut rng)?;
        let mut parts: BTreeMap<usize, DkgSignedVote> = BTreeMap::new();
        let mut acks: BTreeMap<usize, DkgSignedVote> = BTreeMap::new();
        let mut all_acks: BTreeMap<usize, DkgSignedVote> = BTreeMap::new();
        let mut sk_shares: BTreeMap<usize, SecretKeyShare> = BTreeMap::new();

        for node in nodes.iter_mut() {
            parts.insert(node.id() as usize, node.first_vote()?);
        }

        // for cmd in set_of_cmds(num_nodes, 123) {
        //     match cmd {
        //         Cmds::SendParts(from_node, to_nodes) => {
        //             for (to, expt_resp) in to_nodes {
        //                 let actual_resp = (&mut nodes[to])
        //                     .handle_signed_vote(parts[&from_node].clone(), &mut rng)?;
        //                 expt_resp.match_resp(actual_resp, to_update_aux, to_update_sk, id)
        //             }
        //         }
        //         _ => {}
        //     }
        // }
        Ok(())
    }

    // should be (Cmds, expected result when executed);  add a probablity to include nodes that been sent the part/acks/all
    fn set_of_cmds(num_nodes: usize, seed: u64) -> Vec<Cmds> {
        let mut rng = StdRng::seed_from_u64(seed);
        let mut nodes = Node::new(num_nodes);
        // these nodes are required to help other nodes terminate
        let mut active_nodes = Node::active_nodes(&nodes);
        let mut commands = Vec::new();

        while !active_nodes.is_empty() {
            // get a random active node
            let current_node = active_nodes[rng.gen::<usize>() % active_nodes.len()];

            // check if current_node can send part/acks/all_acks; if so randomly choose between 1 of the action
            let parts = nodes[current_node].can_send_parts(&nodes);
            let acks = nodes[current_node].can_send_acks(&nodes);
            let all_acks = nodes[current_node].can_send_all_acks(&nodes);

            // continue if current_node cant progress
            if parts.is_empty() && acks.is_empty() && all_acks.is_empty() {
                continue;
            }

            let mut done = false;
            while !done {
                // randomly send out part/acks/all_acks
                match rng.gen::<usize>() % 3 {
                    0 if !parts.is_empty() => {
                        let to_nodes = Node::sample_nodes(&parts, &mut rng);

                        // update each `to` node and get its (id, response)
                        let to_nodes_resp = to_nodes
                            .into_iter()
                            .map(|to| {
                                let resp =
                                    match (&mut nodes[to]).handled_parts.insert(current_node, true)
                                    {
                                        // updating the `to` with new info node can change its state
                                        None => {
                                            // if `to` node has handled all parts, it should receive a broadcast vote resp
                                            if nodes[to].parts_done() {
                                                MockVoteResponse::BroadcastVote
                                            } else {
                                                MockVoteResponse::WaitingForMoreVotes
                                            }
                                        }
                                        Some(val) => {
                                            // if true, we have already seen it
                                            if val {
                                                MockVoteResponse::IgnoringKnownVote
                                            } else {
                                                MockVoteResponse::WaitingForMoreVotes
                                            }
                                        }
                                    };

                                (to, resp)
                            })
                            .collect();

                        commands.push(Cmds::SendParts(current_node, to_nodes_resp));
                        done = true;
                    }
                    1 if !acks.is_empty() => {
                        let to_nodes = Node::sample_nodes(&acks, &mut rng);

                        let to_nodes_resp = to_nodes
                            .into_iter()
                            .map(|to| {
                                let mut resp = match (&mut nodes[to])
                                    .handled_acks
                                    .insert(current_node, true)
                                {
                                    None => {
                                        if nodes[to].acks_done() {
                                            MockVoteResponse::BroadcastVote
                                        } else {
                                            MockVoteResponse::WaitingForMoreVotes
                                        }
                                    }
                                    Some(val) => {
                                        // if true, we have already seen it
                                        if val {
                                            MockVoteResponse::IgnoringKnownVote
                                        } else {
                                            MockVoteResponse::WaitingForMoreVotes
                                        }
                                    }
                                };
                                (to, resp)
                            })
                            .collect();

                        commands.push(Cmds::SendAcks(current_node, to_nodes_resp));
                        done = true;
                    }
                    2 if !all_acks.is_empty() => {
                        let to_nodes = Node::sample_nodes(&all_acks, &mut rng);

                        let to_nodes_resp = to_nodes
                            .into_iter()
                            .map(|to| {
                                let resp = match (&mut nodes[to])
                                    .handled_all_acks
                                    .insert(current_node, true)
                                {
                                    None => {
                                        if nodes[to].all_acks_done() {
                                            MockVoteResponse::DkgComplete
                                        } else {
                                            MockVoteResponse::WaitingForMoreVotes
                                        }
                                    }
                                    Some(val) => {
                                        // if true, we have already seen it
                                        if val {
                                            MockVoteResponse::IgnoringKnownVote
                                        } else {
                                            MockVoteResponse::WaitingForMoreVotes
                                        }
                                    }
                                };
                                (to, resp)
                            })
                            .collect();

                        commands.push(Cmds::SendAllAcks(current_node, to_nodes_resp));
                        done = true;
                    }
                    _ => {}
                }
            }
            active_nodes = Node::active_nodes(&nodes);
        }
        commands
    }

    // Test helpers
    fn generate_nodes<R: RngCore>(
        num_nodes: usize,
        threshold: usize,
        mut rng: &mut R,
    ) -> Result<Vec<DkgState>> {
        let secret_keys: Vec<SecretKey> = (0..num_nodes).map(|_| bls::rand::random()).collect();
        let pub_keys: BTreeMap<_, _> = secret_keys
            .iter()
            .enumerate()
            .map(|(id, sk)| (id as u8, sk.public_key()))
            .collect();
        secret_keys
            .iter()
            .enumerate()
            .map(|(id, sk)| {
                DkgState::new(id as u8, sk.clone(), pub_keys.clone(), threshold, &mut rng)
            })
            .collect()
    }

    #[derive(Debug)]
    enum Cmds {
        // from, to
        SendParts(usize, Vec<(usize, MockVoteResponse)>),
        SendAcks(usize, Vec<(usize, MockVoteResponse)>),
        SendAllAcks(usize, Vec<(usize, MockVoteResponse)>),
    }

    #[derive(Debug)]
    enum MockVoteResponse {
        WaitingForMoreVotes,
        IgnoringKnownVote,
        BroadcastVote,
        RequestAntiEntropy,
        DkgComplete,
    }

    impl MockVoteResponse {
        pub fn match_resp(
            &self,
            actual_resp: VoteResponse,
            update_votes: Option<&mut BTreeMap<usize, DkgSignedVote>>,
            to_update_sk: Option<&mut BTreeMap<usize, SecretKeyShare>>,
            id: usize,
        ) -> bool {
            if matches!(self, Self::WaitingForMoreVotes)
                && matches!(actual_resp, VoteResponse::WaitingForMoreVotes)
            {
                return true;
            } else if matches!(self, Self::IgnoringKnownVote)
                && matches!(actual_resp, VoteResponse::IgnoringKnownVote)
            {
                return true;
            } else if matches!(self, Self::BroadcastVote) {
                if let VoteResponse::BroadcastVote(vote) = actual_resp {
                    if let Some(to_update) = update_votes {
                        to_update.insert(id, *vote);
                    } else {
                        println!("pass in map to update part/acks/all_acks");
                        return false;
                    }
                    return true;
                } else {
                    return false;
                }
            } else if matches!(self, Self::BroadcastVote) {
                if let VoteResponse::DkgComplete(_, sk) = actual_resp {
                    if let Some(to_update) = to_update_sk {
                        to_update.insert(id, sk);
                    } else {
                        println!("pass in map to update sk_share");
                        return false;
                    }
                    return true;
                } else {
                    return false;
                }
            } else {
                return false;
            }
        }
    }

    #[derive(Debug)]
    struct Node {
        id: usize,
        // Has the current node handled parts, acks, all_acks from another node? whom we have handled
        // randomly handle current node's part/all
        handled_parts: BTreeMap<usize, bool>,
        handled_acks: BTreeMap<usize, bool>,
        handled_all_acks: BTreeMap<usize, bool>,
    }

    impl Node {
        pub fn new(num_nodes: usize) -> Vec<Node> {
            let mut status: BTreeMap<usize, bool> = BTreeMap::new();
            (0..num_nodes).for_each(|id| {
                let _ = status.insert(id, false);
            });
            (0..num_nodes)
                .map(|id| {
                    // we have handled our parts/acks/all_acks by default
                    let mut our_status = status.clone();
                    our_status.insert(id, true);
                    Node {
                        id,
                        handled_parts: our_status.clone(),
                        handled_acks: our_status.clone(),
                        handled_all_acks: our_status,
                    }
                })
                .collect()
        }

        // return the node id's that have not handled self's part
        pub fn can_send_parts(&self, nodes: &Vec<Node>) -> Vec<usize> {
            nodes
                .iter()
                .filter_map(|node| {
                    // if node has not handled self's part
                    if !node.handled_parts[&self.id] {
                        Some(node.id)
                    } else {
                        None
                    }
                })
                .collect()
        }

        pub fn can_send_acks(&self, nodes: &Vec<Node>) -> Vec<usize> {
            // if self has not handled the parts from other nodes, then it cant produce an ack
            // the other node should not have handled self's ack
            if !self.parts_done() {
                return Vec::new();
            }
            nodes
                .iter()
                .filter_map(|node| {
                    if !node.handled_acks[&self.id] {
                        Some(node.id)
                    } else {
                        None
                    }
                })
                .collect()
        }

        pub fn can_send_all_acks(&self, nodes: &Vec<Node>) -> Vec<usize> {
            // self should've handled all the acks (except self's)
            // the other node should not have handled self's all_ack
            if !self.acks_done() {
                return Vec::new();
            }
            nodes
                .iter()
                .filter_map(|node| {
                    if !node.handled_all_acks[&self.id] {
                        Some(node.id)
                    } else {
                        None
                    }
                })
                .collect()
        }

        // returns true if self has recieved/handled all the parts (except itself)
        pub fn parts_done(&self) -> bool {
            self.handled_parts
                .iter()
                .filter(|(&id, _)| id != self.id)
                .all(|(_, &val)| val)
        }

        pub fn acks_done(&self) -> bool {
            self.handled_acks
                .iter()
                .filter(|(&id, _)| id != self.id)
                .all(|(_, &val)| val)
        }

        pub fn all_acks_done(&self) -> bool {
            // check if current_node has completed the dkg round; i.e., it has handled all_acks from all other nodes
            self.handled_all_acks
                .iter()
                .filter(|(&id, _)| id != self.id)
                .all(|(_, &val)| val)
        }

        pub fn active_nodes(nodes: &Vec<Node>) -> Vec<usize> {
            // a node is active, if any of the other node still requires votes from the current node
            // filter out current node as we don't necessarily have to deal with our votes to move forward
            let mut active_nodes = BTreeSet::new();
            nodes.iter().for_each(|node| {
                // check parts
                node.handled_parts.iter().for_each(|(&id, &val)| {
                    // if current node has not handled a part from another node (i.e. false), we need the other node
                    if id != node.id && !val {
                        active_nodes.insert(id);
                    };
                });

                node.handled_acks.iter().for_each(|(&id, &val)| {
                    if id != node.id && !val {
                        active_nodes.insert(id);
                    };
                });

                node.handled_all_acks.iter().for_each(|(&id, &val)| {
                    if id != node.id && !val {
                        active_nodes.insert(id);
                    };
                });
            });
            active_nodes.into_iter().collect()
        }

        // select a subset of node i's from the given list
        pub fn sample_nodes<R: RngCore>(nodes: &Vec<usize>, rng: &mut R) -> Vec<usize> {
            let sample_n_nodes = (rng.gen::<usize>() % nodes.len()) + 1;
            nodes.iter().cloned().choose_multiple(rng, sample_n_nodes)
        }
    }
}
