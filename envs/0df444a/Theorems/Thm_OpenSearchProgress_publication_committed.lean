-- Prove2me | Theorems.Thm_OpenSearchProgress_publication_committed
-- name    : OpenSearchProgress.publication_committed
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T01:01:24.191753+00:00
-- url     : https://prove2.me/theorems/e964a617-6850-4250-b0de-9e2a92c7b192
-- title:
--   A stable publication is committed once a quorum's acknowledgements are counted
-- statement:
--   For every payload type `V`, cluster parameters `P` with `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, every cluster `W` with `Reachable P W`, every node `c`, term `t` and list `Q` of cluster-manager-eligible node ids, such that `c` has won the election and is in term `t`, every cluster state `s`, term `pt` and version `pv` with `W.sent (.publishRequest c s pt pv)`, `s.term = t` and `s.version = (W.node c).lastPublishedVersion`, such that moreover
--
--   - `Q` is a quorum of four configurations: `c`'s last committed and last accepted configurations (`(W.node c).lastCommittedConfiguration.hasQuorum Q = true`, `(W.node c).lastAcceptedConfiguration.hasQuorum Q = true`) and the published state's (`s.lastCommittedConfiguration.hasQuorum Q = true`, `s.lastAcceptedConfiguration.hasQuorum Q = true`);
--   - `c` has counted no acknowledgement yet: `(W.node c).publishVotes.nodes = []`, as right after `handleClientValue`, which empties the publish votes;
--
--   and every cluster `W'` with `PublicationExec P c t Q W W'` in which every member of `Q` is among `c`'s publish votes (`q ∈ (W'.node c).publishVotes.nodes` for every `q ∈ Q`): `Committed W' t s.version`, that is, an `ApplyCommitRequest` for term `t` and version `s.version` has been sent.
--
--   `handlePublishResponse` sends the commit when the votes are a quorum of `c`'s current last committed configuration and of the configuration being published (`isPublishQuorum`, `CoordinationState.java:156-158`). During the period `c`'s last committed configuration can change: applying the commit of its accepted state makes it `c`'s last accepted configuration (Java's `handleCommit` allows this while a publication is in flight), and accepting its own publication makes it `s`'s last committed configuration, which can move it backwards. `Q` must therefore be a quorum of every configuration `c` may be using when the acknowledgement that completes `Q` arrives; otherwise all of `Q` could be counted without a commit.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: Coordinator (handlePublishRequest lines 454-526 with ensureTermAtLeast at 512, startElection 583-602, ensureTermAtLeast 635-641, joinLeaderInTerm 643-657, handleJoin 1267-1287 with handleJoinIgnoringExceptions 1289-1299, publish 1350 with the handleClientValue call at 1404, CoordinatorPublication.handlePublishResponse 1871-1875): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java; CoordinationState (isPublishQuorum lines 156-158, handleStartJoin 213-255, handleJoin 264-339, handleClientValue 348-407, handlePublishRequest 416-460, handlePublishResponse 471-515, handleCommit 523-573) as transcribed by the OpenSearchCoordination mission: https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java; the cluster model, the safety vocabulary and the inductive invariant of the OpenSearchSafety mission (Step, Reachable, Committed, Inv, reachable_inv); for why progress needs a stable period: M. J. Fischer, N. A. Lynch, M. S. Paterson, Impossibility of distributed consensus with one faulty process, J. ACM 32(2), 1985, and C. Dwork, N. Lynch, L. Stockmeyer, Consensus in the presence of partial synchrony, J. ACM 35(2), 1988

import Definitions.Def_OpenSearchProgress
open OpenSearchCoordination OpenSearchSafety OpenSearchProgress

theorem OpenSearchProgress.publication_committed {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId) (hQ : ∀ q ∈ Q, P.eligible q = true)
    (hwon : (W.node c).electionWon = true) (hct : (W.node c).currentTerm = t)
    (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest c s pt pv)) (hst : s.term = t)
    (hsv : s.version = (W.node c).lastPublishedVersion)
    (hquorum : (W.node c).lastCommittedConfiguration.hasQuorum Q = true ∧
      (W.node c).lastAcceptedConfiguration.hasQuorum Q = true ∧
      s.lastCommittedConfiguration.hasQuorum Q = true ∧ s.lastAcceptedConfiguration.hasQuorum Q = true)
    (hpv : (W.node c).publishVotes.nodes = [])
    (W' : Cluster V) (hE : PublicationExec P c t Q W W') (hacks : ∀ q ∈ Q, q ∈ (W'.node c).publishVotes.nodes) :
    Committed W' t s.version := by sorry
