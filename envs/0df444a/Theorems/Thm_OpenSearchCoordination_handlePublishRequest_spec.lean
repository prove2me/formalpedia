-- Prove2me | Theorems.Thm_OpenSearchCoordination_handlePublishRequest_spec
-- name    : OpenSearchCoordination.handlePublishRequest_spec
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:32:42.530083+00:00
-- url     : https://prove2.me/theorems/a6663778-11d4-493b-8fd1-3fcdf4d5dc3a
-- title:
--   handlePublishRequest accepts only a strictly newer state of the current term, Zen1 compatibility aside
-- statement:
--   Let `cs` be a coordination state with `cs.lastAcceptedTerm ≤ cs.currentTerm`, and suppose `cs.handlePublishRequest req = .ok (cs', resp)`. Then:
--
--   - `cs'.lastAcceptedState = req.acceptedState` and `req.acceptedState.term = cs.currentTerm`;
--   - `cs'` has the current term and the local node of `cs`;
--   - `resp` carries the term and the version of `req.acceptedState`;
--   - the accepted state is strictly newer than the old one in the lexicographic (term, version) order — `cs.lastAcceptedTerm < req.acceptedState.term`, or the terms are equal and `cs.lastAcceptedVersion < req.acceptedState.version` — or its term is `ZEN1_BWC_TERM` (0), about which nothing more is stated: this disjunct holds for every term-0 state (the handler accepts a term-0 state that is not newer only in its Zen1 compatibility branch, when that state names a cluster-manager and the last accepted state names none or a different one; the statement does not record this condition);
--   - the join votes, `electionWon`, `startedJoinSinceLastReboot`, `lastPublishedVersion`, `lastPublishedConfiguration` and the publish votes are those of `cs`.
--
--   The hypothesis on `cs` is the first assertion of `invariant()`; without it, a node whose accepted term exceeds its current term would accept a state of a lower term.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: CoordinationState (constructor lines 84-106, isElectionQuorum 144-154, isPublishQuorum 156-158, setInitialState 180-204, handleStartJoin 213-255, handleJoin 264-339, handleClientValue 348-407, handlePublishRequest 416-460, handlePublishResponse 471-515, handleCommit 523-573, invariant 601-611, PersistedState.markLastAcceptedStateAsCommitted 703-728, commitVotingConfiguration 730-740, VoteCollection 750-814), server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java: https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java#L64-L815; CoordinationMetadata.VotingConfiguration (lines 383-449, hasQuorum 405-409): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationMetadata.java#L383-L449; ElectionStrategy (DEFAULT_INSTANCE lines 46-59, isElectionQuorum 68-88): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L44-L110; ClusterState.getVersionOrMetadataVersion (lines 239-244): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/ClusterState.java#L239-L244; Coordinator.ZEN1_BWC_TERM (line 134): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java#L134; the messages StartJoinRequest.java, Join.java, PublishRequest.java, PublishResponse.java, ApplyCommitRequest.java in the same directory; test vectors from server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java (https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java) and CoordinationMetadataTests.java (testVotingConfiguration)

import Definitions.Def_OpenSearchCoordination

theorem OpenSearchCoordination.handlePublishRequest_spec {V : Type} (cs : CoordinationState V) (req : PublishRequest V) (cs' : CoordinationState V)
    (resp : PublishResponse) (hcs : cs.lastAcceptedTerm ≤ cs.currentTerm)
    (h : cs.handlePublishRequest req = .ok (cs', resp)) :
    cs'.lastAcceptedState = req.acceptedState ∧ req.acceptedState.term = cs.currentTerm ∧
    cs'.currentTerm = cs.currentTerm ∧ cs'.localNode = cs.localNode ∧
    resp = ⟨req.acceptedState.term, req.acceptedState.version⟩ ∧
    (cs.lastAcceptedTerm < req.acceptedState.term ∨
      (cs.lastAcceptedTerm = req.acceptedState.term ∧ cs.lastAcceptedVersion < req.acceptedState.version) ∨
      req.acceptedState.term = ZEN1_BWC_TERM) ∧
    cs'.joinVotes = cs.joinVotes ∧ cs'.electionWon = cs.electionWon ∧
    cs'.startedJoinSinceLastReboot = cs.startedJoinSinceLastReboot ∧
    cs'.lastPublishedVersion = cs.lastPublishedVersion ∧
    cs'.lastPublishedConfiguration = cs.lastPublishedConfiguration ∧ cs'.publishVotes = cs.publishVotes := by sorry
