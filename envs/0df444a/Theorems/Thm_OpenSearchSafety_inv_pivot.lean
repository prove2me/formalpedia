-- Prove2me | Theorems.Thm_OpenSearchSafety_inv_pivot
-- name    : OpenSearchSafety.inv_pivot
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:44:14.042528+00:00
-- url     : https://prove2.me/theorems/8edc92c7-1ff7-4fa8-9342-de06ccf5327b
-- title:
--   The pivot of a realized base: its deepest committed ancestor carries one of its two configurations
-- statement:
--   For all `P`, every cluster `W` with `Inv P W`, every key `(bt, bv)` and configurations `x`, `y` with `Realizes P W bt bv x y`, one of the following holds:
--   - there is a sent publication `W.sent (.publishRequest src s pt pv)` with `Committed W s.term s.version` and `Descends W s.term s.version bt bv`, such that every committed `(et, ev)` with `Descends W et ev bt bv` satisfies `Descends W et ev s.term s.version` (it is the deepest committed ancestor-or-self of the base), and `x = s.lastAcceptedConfiguration ∨ y = s.lastAcceptedConfiguration`;
--   - no committed `(et, ev)` satisfies `Descends W et ev bt bv`, and `P.initConfs x`.
--
--   Any pair of configurations a node or a publication can hold for the base thus contains the last configuration committed on its branch, or a bootstrap configuration if nothing is committed on it.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: CoordinationState (the per-node handlers as transcribed by the OpenSearchCoordination mission; handleCommit lines 523-573, isPublishQuorum 156-158, invariant 601-611): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java; Coordinator (the calls into CoordinationState: handleApplyCommit lines 419-452, handlePublishRequest 454-526, startElection 583-602, abdicateTo 604-620, ensureTermAtLeast 635-641, joinLeaderInTerm 643-657, setInitialConfiguration 1101-1161, handleJoin 1267-1299, publish 1350 with the handleClientValue call at 1404, CoordinatorPublication.handlePublishResponse 1871-1876): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java; ClusterBootstrapService (requirements 146-157, onFoundPeersUpdated 176-215, startBootstrap 259-273, checkRequirements 306-335): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ClusterBootstrapService.java#L146-L335; GatewayMetaState.start (persisted state loaded and rebuilt 141-231, remote restore 169-188, synchronous and asynchronous persistence 199-207, nodes without the cluster-manager and data roles 232-255): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/gateway/GatewayMetaState.java#L126-L257; PersistedStateRegistry.addPersistedState (lines 38-41): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/PersistedStateRegistry.java#L38-L41; ElectionStrategy (DEFAULT_INSTANCE lines 46-59): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L44-L110; the randomized safety test CoordinationStateTestCluster (reboot 156-193, runRandomly 279-329, invariant 331-370): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/test/framework/src/main/java/org/opensearch/cluster/coordination/CoordinationStateTestCluster.java and CoordinationStateTests.testSafety (lines 917-924): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java#L917-L924; for comparison, Elastic's TLA+ model ZenWithTerms (HandleCommit 241-250, CommittedValuesDescendantsFromInitialValue 338-347, CommitHasQuorumVsPreviousCommittedConfiguration 349-358): https://github.com/elastic/elasticsearch-formal-models/blob/ca30663506a7e18de9d23fabbc70a369903d7c98/ZenWithTerms/tla/ZenWithTerms.tla

import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_pivot {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (bt : Nat) (bv : Int) (x y : VotingConfiguration) (hr : Realizes P W bt bv x y) :
    (∃ src s pt pv, W.sent (.publishRequest src s pt pv) ∧ Committed W s.term s.version ∧
      Descends W s.term s.version bt bv ∧
      (∀ et ev, Committed W et ev → Descends W et ev bt bv → Descends W et ev s.term s.version) ∧
      (x = s.lastAcceptedConfiguration ∨ y = s.lastAcceptedConfiguration)) ∨
    ((∀ et ev, Committed W et ev → ¬ Descends W et ev bt bv) ∧ P.initConfs x) := by sorry
