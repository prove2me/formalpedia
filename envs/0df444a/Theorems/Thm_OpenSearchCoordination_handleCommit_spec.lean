-- Prove2me | Theorems.Thm_OpenSearchCoordination_handleCommit_spec
-- name    : OpenSearchCoordination.handleCommit_spec
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:32:54.162313+00:00
-- url     : https://prove2.me/theorems/496899b8-431b-48ba-b6bb-9de32880b384
-- title:
--   handleCommit only marks the last accepted state committed
-- statement:
--   For every coordination state `cs`, commit request `c` and state `cs'`: if `cs.handleCommit c = .ok cs'` then
--
--   - the commit is for the last accepted state in the current term: `c.term = cs.currentTerm`, `c.term = cs.lastAcceptedTerm` and `c.version = cs.lastAcceptedVersion`;
--   - `cs'` is `cs` with its last accepted state replaced by `cs.lastAcceptedState.markCommitted` (the committed configuration becomes the accepted one, and a known cluster UUID is marked committed);
--   - in `cs'` the last committed configuration equals the last accepted configuration (the assertion at `CoordinationState.java:572`);
--   - the last accepted configuration, term, version and payload of `cs'` are those of `cs`.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: CoordinationState (constructor lines 84-106, isElectionQuorum 144-154, isPublishQuorum 156-158, setInitialState 180-204, handleStartJoin 213-255, handleJoin 264-339, handleClientValue 348-407, handlePublishRequest 416-460, handlePublishResponse 471-515, handleCommit 523-573, invariant 601-611, PersistedState.markLastAcceptedStateAsCommitted 703-728, commitVotingConfiguration 730-740, VoteCollection 750-814), server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java: https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java#L64-L815; CoordinationMetadata.VotingConfiguration (lines 383-449, hasQuorum 405-409): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationMetadata.java#L383-L449; ElectionStrategy (DEFAULT_INSTANCE lines 46-59, isElectionQuorum 68-88): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L44-L110; ClusterState.getVersionOrMetadataVersion (lines 239-244): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/ClusterState.java#L239-L244; Coordinator.ZEN1_BWC_TERM (line 134): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java#L134; the messages StartJoinRequest.java, Join.java, PublishRequest.java, PublishResponse.java, ApplyCommitRequest.java in the same directory; test vectors from server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java (https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java) and CoordinationMetadataTests.java (testVotingConfiguration)

import Definitions.Def_OpenSearchCoordination

theorem OpenSearchCoordination.handleCommit_spec {V : Type} (cs : CoordinationState V) (c : ApplyCommitRequest) (cs' : CoordinationState V)
    (h : cs.handleCommit c = .ok cs') :
    c.term = cs.currentTerm ∧ c.term = cs.lastAcceptedTerm ∧ c.version = cs.lastAcceptedVersion ∧
    cs' = { cs with lastAcceptedState := cs.lastAcceptedState.markCommitted } ∧
    cs'.lastCommittedConfiguration = cs'.lastAcceptedConfiguration ∧
    cs'.lastAcceptedConfiguration = cs.lastAcceptedConfiguration ∧
    cs'.lastAcceptedTerm = cs.lastAcceptedTerm ∧ cs'.lastAcceptedVersion = cs.lastAcceptedVersion ∧
    cs'.lastAcceptedState.value = cs.lastAcceptedState.value := by sorry
