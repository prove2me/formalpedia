-- Prove2me | Theorems.Thm_OpenSearchSafety_inv_startJoin
-- name    : OpenSearchSafety.inv_startJoin
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:45:53.508022+00:00
-- url     : https://prove2.me/theorems/ca351962-94b1-4b3a-8202-f921381c79ce
-- title:
--   The startJoin step preserves the invariant
-- statement:
--   Let `P` satisfy `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, and let `W` satisfy `Inv P W`. For all nodes `n` and `src` with `P.eligible src = true`, every term `t`, state `cs'` and join `j` with `(W.node n).handleStartJoin ⟨P.dn src, t⟩ = .ok (cs', j)`: `Inv P ((W.set n cs').send (.join j))`.
--
--   The node moves to term `t` and sends its join to `src`. The hypotheses on `P` are not used.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: CoordinationState (the per-node handlers as transcribed by the OpenSearchCoordination mission; handleCommit lines 523-573, isPublishQuorum 156-158, invariant 601-611): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java; Coordinator (the calls into CoordinationState: handleApplyCommit lines 419-452, handlePublishRequest 454-526, startElection 583-602, abdicateTo 604-620, ensureTermAtLeast 635-641, joinLeaderInTerm 643-657, setInitialConfiguration 1101-1161, handleJoin 1267-1299, publish 1350 with the handleClientValue call at 1404, CoordinatorPublication.handlePublishResponse 1871-1876): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java; ClusterBootstrapService (requirements 146-157, onFoundPeersUpdated 176-215, startBootstrap 259-273, checkRequirements 306-335): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ClusterBootstrapService.java#L146-L335; GatewayMetaState.start (persisted state loaded and rebuilt 141-231, remote restore 169-188, synchronous and asynchronous persistence 199-207, nodes without the cluster-manager and data roles 232-255): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/gateway/GatewayMetaState.java#L126-L257; PersistedStateRegistry.addPersistedState (lines 38-41): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/PersistedStateRegistry.java#L38-L41; ElectionStrategy (DEFAULT_INSTANCE lines 46-59): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L44-L110; the randomized safety test CoordinationStateTestCluster (reboot 156-193, runRandomly 279-329, invariant 331-370): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/test/framework/src/main/java/org/opensearch/cluster/coordination/CoordinationStateTestCluster.java and CoordinationStateTests.testSafety (lines 917-924): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java#L917-L924; for comparison, Elastic's TLA+ model ZenWithTerms (HandleCommit 241-250, CommittedValuesDescendantsFromInitialValue 338-347, CommitHasQuorumVsPreviousCommittedConfiguration 349-358): https://github.com/elastic/elasticsearch-formal-models/blob/ca30663506a7e18de9d23fabbc70a369903d7c98/ZenWithTerms/tla/ZenWithTerms.tla

import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_startJoin {V : Type} (P : Params) (_hP : P.InitCompatible)
    (_hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hinv : Inv P W)
    (n src : NodeId) (t : Nat) (cs' : CoordinationState V) (j : Join) (hsrc : P.eligible src = true)
    (h : (W.node n).handleStartJoin ⟨P.dn src, t⟩ = .ok (cs', j)) : Inv P ((W.set n cs').send (.join j)) := by sorry
