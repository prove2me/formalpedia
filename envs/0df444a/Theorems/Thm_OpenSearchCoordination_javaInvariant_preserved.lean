-- Prove2me | Theorems.Thm_OpenSearchCoordination_javaInvariant_preserved
-- name    : OpenSearchCoordination.javaInvariant_preserved
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:34:17.744258+00:00
-- url     : https://prove2.me/theorems/713a4b37-2494-40cd-9acb-a1e59cede97d
-- title:
--   invariant() is preserved by handleJoin, handleClientValue and handlePublishResponse
-- statement:
--   For every monotone election strategy `es` and coordination state `cs` with `cs.javaInvariant es`:
--
--   - if `cs.handleJoin es j = .ok (cs', b)` then `cs'.javaInvariant es`;
--   - if `cs.handleClientValue s = .ok (cs', p)` then `cs'.javaInvariant es`;
--   - if `cs.handlePublishResponse n r = .ok (cs', o)` then `cs'.javaInvariant es`.
--
--   `javaInvariant` is the conjunction of the five assertions of `invariant()` (`CoordinationState.java:601-611`). With `init_javaInvariant` and `handleStartJoin_javaInvariant` this accounts for every handler except `handlePublishRequest` (see `javaInvariant_not_local`), `handleCommit` and `setInitialState`, the three that change the configurations the second assertion reads.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: CoordinationState (constructor lines 84-106, isElectionQuorum 144-154, isPublishQuorum 156-158, setInitialState 180-204, handleStartJoin 213-255, handleJoin 264-339, handleClientValue 348-407, handlePublishRequest 416-460, handlePublishResponse 471-515, handleCommit 523-573, invariant 601-611, PersistedState.markLastAcceptedStateAsCommitted 703-728, commitVotingConfiguration 730-740, VoteCollection 750-814), server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java: https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java#L64-L815; CoordinationMetadata.VotingConfiguration (lines 383-449, hasQuorum 405-409): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationMetadata.java#L383-L449; ElectionStrategy (DEFAULT_INSTANCE lines 46-59, isElectionQuorum 68-88): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L44-L110; ClusterState.getVersionOrMetadataVersion (lines 239-244): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/ClusterState.java#L239-L244; Coordinator.ZEN1_BWC_TERM (line 134): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java#L134; the messages StartJoinRequest.java, Join.java, PublishRequest.java, PublishResponse.java, ApplyCommitRequest.java in the same directory; test vectors from server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java (https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java) and CoordinationMetadataTests.java (testVotingConfiguration)

import Definitions.Def_OpenSearchCoordination

theorem OpenSearchCoordination.javaInvariant_preserved {V : Type} (es : ElectionStrategy) (hes : es.Monotone) (cs : CoordinationState V)
    (hinv : cs.javaInvariant es) :
    (∀ j cs' b, cs.handleJoin es j = .ok (cs', b) → cs'.javaInvariant es) ∧
    (∀ s cs' p, cs.handleClientValue s = .ok (cs', p) → cs'.javaInvariant es) ∧
    (∀ n r cs' o, cs.handlePublishResponse n r = .ok (cs', o) → cs'.javaInvariant es) := by sorry
