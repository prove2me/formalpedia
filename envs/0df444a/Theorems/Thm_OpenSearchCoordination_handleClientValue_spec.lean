-- Prove2me | Theorems.Thm_OpenSearchCoordination_handleClientValue_spec
-- name    : OpenSearchCoordination.handleClientValue_spec
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:33:41.432455+00:00
-- url     : https://prove2.me/theorems/e6498eac-9d67-4232-add7-37bf878f45a1
-- title:
--   handleClientValue publishes only as an elected node, in its term, above the last version, reconfiguring only safely
-- statement:
--   For every coordination state `cs`, cluster state `s`, state `cs'` and publish request `p`: if `cs.handleClientValue s = .ok (cs', p)` then
--
--   - `cs.electionWon = true`;
--   - `cs.lastPublishedVersion = cs.lastAcceptedVersion`: the node has accepted its own last publication;
--   - `s.term = cs.currentTerm` and `cs.lastAcceptedVersion < s.version` (so the new version is above the last published one);
--   - `s` keeps the node's last accepted configuration (`s.lastAcceptedConfiguration = cs.lastAcceptedConfiguration`), or no reconfiguration is pending (`cs.lastCommittedConfiguration = cs.lastAcceptedConfiguration`);
--   - the node's join votes are a quorum of the new accepted configuration: `cs.joinVotes.isQuorum s.lastAcceptedConfiguration = true`;
--   - `p` is the publish request of `s`, and `cs'` is `cs` with `lastPublishedVersion := s.version`, `lastPublishedConfiguration := s.lastAcceptedConfiguration` and empty publish votes.
--
--   The asserted precondition that `s` keeps the node's last committed configuration (`clientValueContract`, `CoordinationState.java:397-398`) is a caller contract and is not part of the statement.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: CoordinationState (constructor lines 84-106, isElectionQuorum 144-154, isPublishQuorum 156-158, setInitialState 180-204, handleStartJoin 213-255, handleJoin 264-339, handleClientValue 348-407, handlePublishRequest 416-460, handlePublishResponse 471-515, handleCommit 523-573, invariant 601-611, PersistedState.markLastAcceptedStateAsCommitted 703-728, commitVotingConfiguration 730-740, VoteCollection 750-814), server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java: https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java#L64-L815; CoordinationMetadata.VotingConfiguration (lines 383-449, hasQuorum 405-409): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationMetadata.java#L383-L449; ElectionStrategy (DEFAULT_INSTANCE lines 46-59, isElectionQuorum 68-88): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L44-L110; ClusterState.getVersionOrMetadataVersion (lines 239-244): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/ClusterState.java#L239-L244; Coordinator.ZEN1_BWC_TERM (line 134): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java#L134; the messages StartJoinRequest.java, Join.java, PublishRequest.java, PublishResponse.java, ApplyCommitRequest.java in the same directory; test vectors from server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java (https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java) and CoordinationMetadataTests.java (testVotingConfiguration)

import Definitions.Def_OpenSearchCoordination

theorem OpenSearchCoordination.handleClientValue_spec {V : Type} (cs : CoordinationState V) (s : ClusterState V) (cs' : CoordinationState V)
    (p : PublishRequest V) (h : cs.handleClientValue s = .ok (cs', p)) :
    cs.electionWon = true ∧ cs.lastPublishedVersion = cs.lastAcceptedVersion ∧ s.term = cs.currentTerm ∧
    cs.lastAcceptedVersion < s.version ∧
    (s.lastAcceptedConfiguration = cs.lastAcceptedConfiguration ∨
      cs.lastCommittedConfiguration = cs.lastAcceptedConfiguration) ∧
    cs.joinVotes.isQuorum s.lastAcceptedConfiguration = true ∧
    p = ⟨s⟩ ∧ cs' = { cs with lastPublishedVersion := s.version,
                               lastPublishedConfiguration := s.lastAcceptedConfiguration,
                               publishVotes := VoteCollection.empty } := by sorry
