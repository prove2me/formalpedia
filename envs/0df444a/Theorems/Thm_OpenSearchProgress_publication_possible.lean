-- Prove2me | Theorems.Thm_OpenSearchProgress_publication_possible
-- name    : OpenSearchProgress.publication_possible
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T01:01:34.161038+00:00
-- url     : https://prove2.me/theorems/86452495-01e3-4eee-bd22-459ad2d84958
-- title:
--   Stable publications are committed: some stable publication execution reaches the commit
-- statement:
--   For every payload type `V`, cluster parameters `P` with `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, every cluster `W` with `Reachable P W`, every node `c`, term `t` and list `Q` of cluster-manager-eligible node ids, such that `c` has won the election and is in term `t`, every cluster state `s`, term `pt` and version `pv` with `W.sent (.publishRequest c s pt pv)`, `s.term = t` and `s.version = (W.node c).lastPublishedVersion`, such that
--
--   - `Q` is a quorum of `(W.node c).lastCommittedConfiguration`, `(W.node c).lastAcceptedConfiguration`, `s.lastCommittedConfiguration` and `s.lastAcceptedConfiguration`;
--   - every member of `Q` is in a term at most `t`: `(W.node q).currentTerm ≤ t` for every `q ∈ Q`;
--
--   there is a cluster `W'` with `PublicationExec P c t Q W W'` and `Committed W' t s.version`. Unlike `publication_committed`, `c` may already have counted acknowledgements at `W`.
--
--   The theorem asserts only that such an execution exists; if the publication is already committed at `W`, the empty execution is one. In the proof's witness, each node of `Q` below term `t` handles a start-join from `c` for `t`, each node of `Q` accepts `s` and acknowledges it unless it already has, and `c` counts the acknowledgements, handling one of them a second time at the end; the stable period allows each such step.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: Coordinator (handlePublishRequest lines 454-526 with ensureTermAtLeast at 512, startElection 583-602, ensureTermAtLeast 635-641, joinLeaderInTerm 643-657, handleJoin 1267-1287 with handleJoinIgnoringExceptions 1289-1299, publish 1350 with the handleClientValue call at 1404, CoordinatorPublication.handlePublishResponse 1871-1875): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java; CoordinationState (isPublishQuorum lines 156-158, handleStartJoin 213-255, handleJoin 264-339, handleClientValue 348-407, handlePublishRequest 416-460, handlePublishResponse 471-515, handleCommit 523-573) as transcribed by the OpenSearchCoordination mission: https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java; the cluster model, the safety vocabulary and the inductive invariant of the OpenSearchSafety mission (Step, Reachable, Committed, Inv, reachable_inv); for why progress needs a stable period: M. J. Fischer, N. A. Lynch, M. S. Paterson, Impossibility of distributed consensus with one faulty process, J. ACM 32(2), 1985, and C. Dwork, N. Lynch, L. Stockmeyer, Consensus in the presence of partial synchrony, J. ACM 35(2), 1988

import Definitions.Def_OpenSearchProgress
open OpenSearchCoordination OpenSearchSafety OpenSearchProgress

theorem OpenSearchProgress.publication_possible {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId) (hQ : ∀ q ∈ Q, P.eligible q = true)
    (hwon : (W.node c).electionWon = true) (hct : (W.node c).currentTerm = t)
    (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest c s pt pv)) (hst : s.term = t)
    (hsv : s.version = (W.node c).lastPublishedVersion)
    (hquorum : (W.node c).lastCommittedConfiguration.hasQuorum Q = true ∧
      (W.node c).lastAcceptedConfiguration.hasQuorum Q = true ∧
      s.lastCommittedConfiguration.hasQuorum Q = true ∧ s.lastAcceptedConfiguration.hasQuorum Q = true)
    (hterm : ∀ q ∈ Q, (W.node q).currentTerm ≤ t) :
    ∃ W', PublicationExec P c t Q W W' ∧ Committed W' t s.version := by sorry
