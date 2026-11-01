-- Prove2me | Theorems.Thm_OpenSearchSafety_inv_lineage
-- name    : OpenSearchSafety.inv_lineage
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:43:34.878357+00:00
-- url     : https://prove2.me/theorems/c6ed7753-597f-4a2e-bee4-e73dc88c1e05
-- title:
--   Path summary: across uncommitted publications, an accepted configuration stays in force
-- statement:
--   For all `P`, every cluster `W` with `Inv P W` and two sent publications `W.sent (.publishRequest srcD sD ptD pvD)` and `W.sent (.publishRequest srcE sE ptE pvE)` such that
--   - `Descends W sD.term sD.version sE.term sE.version` and `¬ (sD.term = sE.term ∧ sD.version = sE.version)`, and
--   - no committed key lies strictly between them: every committed `(ft, fv)` with `Descends W sD.term sD.version ft fv` and `Descends W ft fv sE.term sE.version` is `(sD.term, sD.version)` or `(sE.term, sE.version)`,
--
--   we have `sE.lastCommittedConfiguration = sD.lastAcceptedConfiguration ∨ sE.lastAcceptedConfiguration = sD.lastAcceptedConfiguration`.
--
--   The last committed configuration is copied from the parent unless the parent is committed, and the last accepted configuration changes only when the last committed configuration is the parent's last accepted one (`pub_parent`, the transcription of `handleClientValue`'s reconfiguration guard and of the asserted copying of the committed configuration). Hence at most one reconfiguration is in flight between commits: the configuration accepted at `D` is one of the two configurations of every publication `E` that descends from `D`, with a different key and no committed key strictly between them (`D` and `E` themselves may be committed).
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: CoordinationState (the per-node handlers as transcribed by the OpenSearchCoordination mission; handleCommit lines 523-573, isPublishQuorum 156-158, invariant 601-611): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java; Coordinator (the calls into CoordinationState: handleApplyCommit lines 419-452, handlePublishRequest 454-526, startElection 583-602, abdicateTo 604-620, ensureTermAtLeast 635-641, joinLeaderInTerm 643-657, setInitialConfiguration 1101-1161, handleJoin 1267-1299, publish 1350 with the handleClientValue call at 1404, CoordinatorPublication.handlePublishResponse 1871-1876): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java; ClusterBootstrapService (requirements 146-157, onFoundPeersUpdated 176-215, startBootstrap 259-273, checkRequirements 306-335): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ClusterBootstrapService.java#L146-L335; GatewayMetaState.start (persisted state loaded and rebuilt 141-231, remote restore 169-188, synchronous and asynchronous persistence 199-207, nodes without the cluster-manager and data roles 232-255): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/gateway/GatewayMetaState.java#L126-L257; PersistedStateRegistry.addPersistedState (lines 38-41): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/PersistedStateRegistry.java#L38-L41; ElectionStrategy (DEFAULT_INSTANCE lines 46-59): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L44-L110; the randomized safety test CoordinationStateTestCluster (reboot 156-193, runRandomly 279-329, invariant 331-370): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/test/framework/src/main/java/org/opensearch/cluster/coordination/CoordinationStateTestCluster.java and CoordinationStateTests.testSafety (lines 917-924): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java#L917-L924; for comparison, Elastic's TLA+ model ZenWithTerms (HandleCommit 241-250, CommittedValuesDescendantsFromInitialValue 338-347, CommitHasQuorumVsPreviousCommittedConfiguration 349-358): https://github.com/elastic/elasticsearch-formal-models/blob/ca30663506a7e18de9d23fabbc70a369903d7c98/ZenWithTerms/tla/ZenWithTerms.tla

import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_lineage {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (srcD srcE : NodeId) (sD sE : ClusterState V) (ptD ptE : Nat) (pvD pvE : Int)
    (hD : W.sent (.publishRequest srcD sD ptD pvD)) (hE : W.sent (.publishRequest srcE sE ptE pvE))
    (h : Descends W sD.term sD.version sE.term sE.version)
    (hne : ¬ (sD.term = sE.term ∧ sD.version = sE.version))
    (hint : ∀ ft fv, Committed W ft fv → Descends W sD.term sD.version ft fv → Descends W ft fv sE.term sE.version →
      (ft = sD.term ∧ fv = sD.version) ∨ (ft = sE.term ∧ fv = sE.version)) :
    sE.lastCommittedConfiguration = sD.lastAcceptedConfiguration ∨
    sE.lastAcceptedConfiguration = sD.lastAcceptedConfiguration := by sorry
