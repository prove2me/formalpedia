-- Prove2me | Theorems.Thm_OpenSearchCoordination_javaInvariant_not_local
-- name    : OpenSearchCoordination.javaInvariant_not_local
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:34:26.921055+00:00
-- url     : https://prove2.me/theorems/00ecd6c9-7d4c-4dc7-94da-341770c43dc6
-- title:
--   invariant() is not preserved by handlePublishRequest in isolation
-- statement:
--   There exist a coordination state `cs` and a publish request `p` (payload type `Unit`) such that `cs` satisfies `javaInvariant` for the default election strategy, `cs.handlePublishRequest p` succeeds with some state `cs'` and response, and `cs'` does not satisfy `javaInvariant` for the default strategy.
--
--   In the witness, node 0 is in term 1 with an accepted term-0 state whose configurations are {1, 2, 3}; it holds a join vote of node 4 and has not won an election. It accepts a term-1 state whose configurations are {4}; its join votes are then an election quorum while `electionWon` is false. Whether `invariant()` holds along an execution therefore depends on what the other nodes did: it is a property of the cluster, which the `OpenSearchSafety` mission proves at every cluster-manager-eligible node of its cluster model, assuming compatible bootstrap configurations and the default election strategy (`OpenSearchSafety.javaInvariant_reachable`).
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: CoordinationState (constructor lines 84-106, isElectionQuorum 144-154, isPublishQuorum 156-158, setInitialState 180-204, handleStartJoin 213-255, handleJoin 264-339, handleClientValue 348-407, handlePublishRequest 416-460, handlePublishResponse 471-515, handleCommit 523-573, invariant 601-611, PersistedState.markLastAcceptedStateAsCommitted 703-728, commitVotingConfiguration 730-740, VoteCollection 750-814), server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java: https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java#L64-L815; CoordinationMetadata.VotingConfiguration (lines 383-449, hasQuorum 405-409): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationMetadata.java#L383-L449; ElectionStrategy (DEFAULT_INSTANCE lines 46-59, isElectionQuorum 68-88): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L44-L110; ClusterState.getVersionOrMetadataVersion (lines 239-244): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/ClusterState.java#L239-L244; Coordinator.ZEN1_BWC_TERM (line 134): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java#L134; the messages StartJoinRequest.java, Join.java, PublishRequest.java, PublishResponse.java, ApplyCommitRequest.java in the same directory; test vectors from server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java (https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java) and CoordinationMetadataTests.java (testVotingConfiguration)

import Definitions.Def_OpenSearchCoordination

theorem OpenSearchCoordination.javaInvariant_not_local :
    ∃ (cs : CoordinationState Unit) (p : PublishRequest Unit) (cs' : CoordinationState Unit) (r : PublishResponse),
      cs.javaInvariant ElectionStrategy.DEFAULT_INSTANCE ∧ cs.handlePublishRequest p = .ok (cs', r) ∧
      ¬ cs'.javaInvariant ElectionStrategy.DEFAULT_INSTANCE := by sorry
