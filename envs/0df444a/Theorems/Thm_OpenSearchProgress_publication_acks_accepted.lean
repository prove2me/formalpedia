-- Prove2me | Theorems.Thm_OpenSearchProgress_publication_acks_accepted
-- name    : OpenSearchProgress.publication_acks_accepted
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T01:01:12.845243+00:00
-- url     : https://prove2.me/theorems/634bb895-9e56-4b3b-a2f4-2fdf67301f22
-- title:
--   Acknowledgements keep counting during a stable publication
-- statement:
--   For every payload type `V`, cluster parameters `P` with `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, every cluster `W` with `Reachable P W`, every node `c`, term `t` and list `Q` of cluster-manager-eligible node ids, such that `c` has won the election and is in term `t` (`(W.node c).electionWon = true`, `(W.node c).currentTerm = t`), every cluster state `s`, term `pt` and version `pv` such that `c` has sent the publication of `s` with ghost parent `(pt, pv)` (`W.sent (.publishRequest c s pt pv)`), `s.term = t` and `s.version = (W.node c).lastPublishedVersion` (it is `c`'s latest publication), and every cluster `W'` with `PublicationExec P c t Q W W'`:
--
--   1. every `q ∈ Q` with `(W'.node q).currentTerm = t` has already acknowledged `(t, s.version)` to `c` (`W'.sent (.publishResponse q c ⟨t, s.version⟩)`) or accepts `s` now: `(W'.node q).handlePublishRequest ⟨s⟩ = .ok (cs', r)` for some `cs'` and `r`;
--   2. for every `q ∈ Q` with `W'.sent (.publishResponse q c ⟨t, s.version⟩)`, `c` accepts that acknowledgement and counts it: `(W'.node c).handlePublishResponse (P.dn q) ⟨t, s.version⟩ = .ok (cs', o)` for some `cs'` and `o` with `q ∈ cs'.publishVotes.nodes`.
--
--   Item 1 covers only the nodes of `Q` that are in term `t` at `W'`. The period allows a node of `Q` below term `t` to reach it by handling a start-join from `c` for `t`, as `Coordinator.ensureTermAtLeast` does when a node receives a publication of a higher term, after which item 1 applies to it; the witness of `publication_possible` uses this step, but this theorem does not state that it is enabled. A node of `Q` above term `t` stays above it, so item 1 never applies to it.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: Coordinator (handlePublishRequest lines 454-526 with ensureTermAtLeast at 512, startElection 583-602, ensureTermAtLeast 635-641, joinLeaderInTerm 643-657, handleJoin 1267-1287 with handleJoinIgnoringExceptions 1289-1299, publish 1350 with the handleClientValue call at 1404, CoordinatorPublication.handlePublishResponse 1871-1875): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java; CoordinationState (isPublishQuorum lines 156-158, handleStartJoin 213-255, handleJoin 264-339, handleClientValue 348-407, handlePublishRequest 416-460, handlePublishResponse 471-515, handleCommit 523-573) as transcribed by the OpenSearchCoordination mission: https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java; the cluster model, the safety vocabulary and the inductive invariant of the OpenSearchSafety mission (Step, Reachable, Committed, Inv, reachable_inv); for why progress needs a stable period: M. J. Fischer, N. A. Lynch, M. S. Paterson, Impossibility of distributed consensus with one faulty process, J. ACM 32(2), 1985, and C. Dwork, N. Lynch, L. Stockmeyer, Consensus in the presence of partial synchrony, J. ACM 35(2), 1988

import Definitions.Def_OpenSearchProgress
open OpenSearchCoordination OpenSearchSafety OpenSearchProgress

theorem OpenSearchProgress.publication_acks_accepted {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId) (hQ : ∀ q ∈ Q, P.eligible q = true)
    (hwon : (W.node c).electionWon = true) (hct : (W.node c).currentTerm = t)
    (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest c s pt pv)) (hst : s.term = t)
    (hsv : s.version = (W.node c).lastPublishedVersion)
    (W' : Cluster V) (hE : PublicationExec P c t Q W W') :
    (∀ q ∈ Q, (W'.node q).currentTerm = t →
      W'.sent (.publishResponse q c ⟨t, s.version⟩) ∨
      ∃ cs' r, (W'.node q).handlePublishRequest ⟨s⟩ = .ok (cs', r)) ∧
    (∀ q ∈ Q, W'.sent (.publishResponse q c ⟨t, s.version⟩) →
      ∃ cs' o, (W'.node c).handlePublishResponse (P.dn q) ⟨t, s.version⟩ = .ok (cs', o) ∧
        q ∈ cs'.publishVotes.nodes) := by sorry
