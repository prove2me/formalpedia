-- Prove2me | Theorems.Thm_OpenSearchCoordination_handleStartJoin_spec
-- name    : OpenSearchCoordination.handleStartJoin_spec
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:32:33.305473+00:00
-- url     : https://prove2.me/theorems/d6f872b6-7003-403f-bb0b-d4facd85f81f
-- title:
--   handleStartJoin succeeds exactly when the term increases; it moves to that term and votes for the requester
-- statement:
--   For every coordination state `cs`, start-join request `req`, state `cs'` and join `j`: `cs.handleStartJoin req = .ok (cs', j)` holds iff all of the following hold:
--
--   - `cs.currentTerm < req.term`, and `cs'.currentTerm = req.term`;
--   - `cs'` has the last accepted state and the local node of `cs`;
--   - `cs'.startedJoinSinceLastReboot = true` and `cs'.electionWon = false`;
--   - the join votes and the publish votes of `cs'` are `VoteCollection.empty`;
--   - `cs'.lastPublishedVersion = 0` and `cs'.lastPublishedConfiguration = cs.lastAcceptedConfiguration`;
--   - `j` is the join from `cs.localNode` to `req.sourceNode` in term `req.term`, carrying `cs.lastAcceptedTerm` and `cs.lastAcceptedVersionOrMetadataVersion` (the last accepted state's version, or its metadata version if its term is 0).
--
--   The conditions on `cs'` fix all nine of its fields, so the result of a successful call is determined; a request whose term is not above the current term is rejected.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: CoordinationState (constructor lines 84-106, isElectionQuorum 144-154, isPublishQuorum 156-158, setInitialState 180-204, handleStartJoin 213-255, handleJoin 264-339, handleClientValue 348-407, handlePublishRequest 416-460, handlePublishResponse 471-515, handleCommit 523-573, invariant 601-611, PersistedState.markLastAcceptedStateAsCommitted 703-728, commitVotingConfiguration 730-740, VoteCollection 750-814), server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java: https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java#L64-L815; CoordinationMetadata.VotingConfiguration (lines 383-449, hasQuorum 405-409): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationMetadata.java#L383-L449; ElectionStrategy (DEFAULT_INSTANCE lines 46-59, isElectionQuorum 68-88): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L44-L110; ClusterState.getVersionOrMetadataVersion (lines 239-244): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/ClusterState.java#L239-L244; Coordinator.ZEN1_BWC_TERM (line 134): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java#L134; the messages StartJoinRequest.java, Join.java, PublishRequest.java, PublishResponse.java, ApplyCommitRequest.java in the same directory; test vectors from server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java (https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java) and CoordinationMetadataTests.java (testVotingConfiguration)

import Definitions.Def_OpenSearchCoordination

theorem OpenSearchCoordination.handleStartJoin_spec {V : Type} (cs : CoordinationState V) (req : StartJoinRequest) (cs' : CoordinationState V)
    (j : Join) :
    cs.handleStartJoin req = .ok (cs', j) ↔
      cs.currentTerm < req.term ∧ cs'.currentTerm = req.term ∧ cs'.lastAcceptedState = cs.lastAcceptedState ∧
      cs'.localNode = cs.localNode ∧ cs'.startedJoinSinceLastReboot = true ∧ cs'.electionWon = false ∧
      cs'.joinVotes = VoteCollection.empty ∧ cs'.publishVotes = VoteCollection.empty ∧
      cs'.lastPublishedVersion = 0 ∧ cs'.lastPublishedConfiguration = cs.lastAcceptedConfiguration ∧
      j = ⟨cs.localNode, req.sourceNode, req.term, cs.lastAcceptedTerm, cs.lastAcceptedVersionOrMetadataVersion⟩ := by sorry
