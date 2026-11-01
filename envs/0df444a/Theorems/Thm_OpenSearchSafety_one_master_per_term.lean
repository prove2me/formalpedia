-- Prove2me | Theorems.Thm_OpenSearchSafety_one_master_per_term
-- name    : OpenSearchSafety.one_master_per_term
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:47:29.82784+00:00
-- url     : https://prove2.me/theorems/c1f16d50-e34d-41ec-9c8b-e6075c245929
-- title:
--   One cluster-manager per term
-- statement:
--   For every payload type `V`, cluster parameters `P` with `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, every cluster `W` with `Reachable P W`, all nodes `a`, `b`, cluster states `s`, `s'`, terms `pt`, `pt'` and versions `pv`, `pv'`: if `W.sent (.publishRequest a s pt pv)`, `W.sent (.publishRequest b s' pt' pv')` and `s.term = s'.term`, then `a = b`.
--
--   Two publications of the same term come from the same node. This is the first property checked by OpenSearch's randomized `CoordinationStateTestCluster`.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: CoordinationState (the per-node handlers as transcribed by the OpenSearchCoordination mission; handleCommit lines 523-573, isPublishQuorum 156-158, invariant 601-611): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java; Coordinator (the calls into CoordinationState: handleApplyCommit lines 419-452, handlePublishRequest 454-526, startElection 583-602, abdicateTo 604-620, ensureTermAtLeast 635-641, joinLeaderInTerm 643-657, setInitialConfiguration 1101-1161, handleJoin 1267-1299, publish 1350 with the handleClientValue call at 1404, CoordinatorPublication.handlePublishResponse 1871-1876): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java; ClusterBootstrapService (requirements 146-157, onFoundPeersUpdated 176-215, startBootstrap 259-273, checkRequirements 306-335): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ClusterBootstrapService.java#L146-L335; GatewayMetaState.start (persisted state loaded and rebuilt 141-231, remote restore 169-188, synchronous and asynchronous persistence 199-207, nodes without the cluster-manager and data roles 232-255): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/gateway/GatewayMetaState.java#L126-L257; PersistedStateRegistry.addPersistedState (lines 38-41): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/PersistedStateRegistry.java#L38-L41; ElectionStrategy (DEFAULT_INSTANCE lines 46-59): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L44-L110; the randomized safety test CoordinationStateTestCluster (reboot 156-193, runRandomly 279-329, invariant 331-370): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/test/framework/src/main/java/org/opensearch/cluster/coordination/CoordinationStateTestCluster.java and CoordinationStateTests.testSafety (lines 917-924): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java#L917-L924; for comparison, Elastic's TLA+ model ZenWithTerms (HandleCommit 241-250, CommittedValuesDescendantsFromInitialValue 338-347, CommitHasQuorumVsPreviousCommittedConfiguration 349-358): https://github.com/elastic/elasticsearch-formal-models/blob/ca30663506a7e18de9d23fabbc70a369903d7c98/ZenWithTerms/tla/ZenWithTerms.tla

import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.one_master_per_term {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (a b : NodeId) (s s' : ClusterState V) (pt pt' : Nat) (pv pv' : Int)
    (h₁ : W.sent (.publishRequest a s pt pv)) (h₂ : W.sent (.publishRequest b s' pt' pv'))
    (ht : s.term = s'.term) : a = b := by sorry
