-- Prove2me | Theorems.Thm_OpenSearchCoordination_handleStartJoin_javaInvariant
-- name    : OpenSearchCoordination.handleStartJoin_javaInvariant
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:34:09.007203+00:00
-- url     : https://prove2.me/theorems/81cfe557-a0fb-4175-a2b4-847c594c8423
-- title:
--   handleStartJoin re-establishes invariant()
-- statement:
--   For every election strategy `es` and coordination state `cs` with `cs.lastAcceptedTerm ≤ cs.currentTerm` (nothing else is assumed): if `cs.handleStartJoin r = .ok (cs', j)` then `cs'.javaInvariant es`. Moving to a higher term discards the votes and the election, which makes the last four assertions of `invariant()` hold whatever held before; the first, assumed of `cs`, survives because the current term grows and the accepted state is unchanged.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: CoordinationState (constructor lines 84-106, isElectionQuorum 144-154, isPublishQuorum 156-158, setInitialState 180-204, handleStartJoin 213-255, handleJoin 264-339, handleClientValue 348-407, handlePublishRequest 416-460, handlePublishResponse 471-515, handleCommit 523-573, invariant 601-611, PersistedState.markLastAcceptedStateAsCommitted 703-728, commitVotingConfiguration 730-740, VoteCollection 750-814), server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java: https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java#L64-L815; CoordinationMetadata.VotingConfiguration (lines 383-449, hasQuorum 405-409): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationMetadata.java#L383-L449; ElectionStrategy (DEFAULT_INSTANCE lines 46-59, isElectionQuorum 68-88): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L44-L110; ClusterState.getVersionOrMetadataVersion (lines 239-244): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/ClusterState.java#L239-L244; Coordinator.ZEN1_BWC_TERM (line 134): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java#L134; the messages StartJoinRequest.java, Join.java, PublishRequest.java, PublishResponse.java, ApplyCommitRequest.java in the same directory; test vectors from server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java (https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java) and CoordinationMetadataTests.java (testVotingConfiguration)

import Definitions.Def_OpenSearchCoordination

theorem OpenSearchCoordination.handleStartJoin_javaInvariant {V : Type} (es : ElectionStrategy) (cs : CoordinationState V) (r : StartJoinRequest)
    (cs' : CoordinationState V) (j : Join) (hcs : cs.lastAcceptedTerm ≤ cs.currentTerm)
    (h : cs.handleStartJoin r = .ok (cs', j)) : cs'.javaInvariant es := by sorry
