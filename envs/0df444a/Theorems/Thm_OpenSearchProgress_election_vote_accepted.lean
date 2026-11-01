-- Prove2me | Theorems.Thm_OpenSearchProgress_election_vote_accepted
-- name    : OpenSearchProgress.election_vote_accepted
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T01:00:38.466726+00:00
-- url     : https://prove2.me/theorems/bb3d9724-20a9-418a-9d7c-edc14afa21e6
-- title:
--   Votes keep counting during a stable election: once in the election term, the candidate accepts every voter's join for that term whenever it arrives
-- statement:
--   For every payload type `V`, cluster parameters `P` with `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, every cluster `W` with `Reachable P W`, every node `c`, term `t` and list of node ids `Q` such that
--
--   - `c` and every member of `Q` are cluster-manager-eligible: `P.eligible c = true` and `P.eligible q = true` for every `q ∈ Q`;
--   - `c` and every member of `Q` are in a term below `t`: `(W.node q).currentTerm < t` for `q = c` and for every `q ∈ Q`;
--   - every member of `Q` has an accepted state no fresher than `c`'s, compared as `handleJoin` compares a join with the node's state: `(W.node q).lastAcceptedTerm < (W.node c).lastAcceptedTerm`, or the two terms are equal and `(W.node q).lastAcceptedVersionOrMetadataVersion ≤ (W.node c).lastAcceptedVersionOrMetadataVersion`;
--   - `c` has a nonempty last accepted configuration (as after a bootstrap or after accepting a publication): `(W.node c).lastAcceptedConfiguration.isEmpty = false`;
--
--   and every cluster `W'` with `ElectionExec P c t Q (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion W W'` (a stable election period for `c`, `t` and `Q` starting at `W`) in which `c` is in term `t`, `(W'.node c).currentTerm = t`: for every join `j` with `W'.sent (.join j)`, `j.sourceNode.id ∈ Q`, `j.targetNode.id = c` and `j.term = t`, there are a state `cs'` and a flag `b` with `(W'.node c).handleJoin P.strategy j = .ok (cs', b)` and `j.sourceNode.id ∈ cs'.joinVotes.nodes`.
--
--   Whatever has happened since the period started (deliveries in any order, duplicates, the steps the period allows the other nodes, commits at `c` and at the voters), once `c` is in term `t` each voter's join for `t` is accepted by `c` whenever it is delivered, and the vote is counted. A join delivered while `c` is still below `t` is not covered, and is rejected (the terms differ): in the model a voter may handle `c`'s start-join request for `t` before `c` does.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: Coordinator (handlePublishRequest lines 454-526 with ensureTermAtLeast at 512, startElection 583-602, ensureTermAtLeast 635-641, joinLeaderInTerm 643-657, handleJoin 1267-1287 with handleJoinIgnoringExceptions 1289-1299, publish 1350 with the handleClientValue call at 1404, CoordinatorPublication.handlePublishResponse 1871-1875): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java; CoordinationState (isPublishQuorum lines 156-158, handleStartJoin 213-255, handleJoin 264-339, handleClientValue 348-407, handlePublishRequest 416-460, handlePublishResponse 471-515, handleCommit 523-573) as transcribed by the OpenSearchCoordination mission: https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java; the cluster model, the safety vocabulary and the inductive invariant of the OpenSearchSafety mission (Step, Reachable, Committed, Inv, reachable_inv); for why progress needs a stable period: M. J. Fischer, N. A. Lynch, M. S. Paterson, Impossibility of distributed consensus with one faulty process, J. ACM 32(2), 1985, and C. Dwork, N. Lynch, L. Stockmeyer, Consensus in the presence of partial synchrony, J. ACM 35(2), 1988

import Definitions.Def_OpenSearchProgress
open OpenSearchCoordination OpenSearchSafety OpenSearchProgress

theorem OpenSearchProgress.election_vote_accepted {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId) (hc : P.eligible c = true) (hQ : ∀ q ∈ Q, P.eligible q = true)
    (hterm : ∀ q, q = c ∨ q ∈ Q → (W.node q).currentTerm < t)
    (hfresh : ∀ q ∈ Q, (W.node q).lastAcceptedTerm < (W.node c).lastAcceptedTerm ∨
      ((W.node q).lastAcceptedTerm = (W.node c).lastAcceptedTerm ∧
        (W.node q).lastAcceptedVersionOrMetadataVersion ≤ (W.node c).lastAcceptedVersionOrMetadataVersion))
    (hconf : (W.node c).lastAcceptedConfiguration.isEmpty = false)
    (W' : Cluster V)
    (hE : ElectionExec P c t Q (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion W W')
    (hct : (W'.node c).currentTerm = t) (j : Join) (hj : W'.sent (.join j)) (hsrc : j.sourceNode.id ∈ Q)
    (htgt : j.targetNode.id = c) (hjt : j.term = t) :
    ∃ cs' b, (W'.node c).handleJoin P.strategy j = .ok (cs', b) ∧ j.sourceNode.id ∈ cs'.joinVotes.nodes := by sorry
