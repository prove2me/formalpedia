-- Prove2me | Theorems.Thm_OpenSearchCoordination_handleJoin_spec
-- name    : OpenSearchCoordination.handleJoin_spec
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:33:13.338203+00:00
-- url     : https://prove2.me/theorems/17347ac3-8dcb-4b0e-b2ff-5488d658ecc4
-- title:
--   handleJoin: which votes are counted, and electionWon recomputed
-- statement:
--   For every election strategy `es`, coordination state `cs`, join `j`, state `cs'` and flag `b`: if `cs.handleJoin es j = .ok (cs', b)` then
--
--   - the join is for the current term: `j.term = cs.currentTerm`;
--   - the node has handled a start-join since its last restart (`cs.startedJoinSinceLastReboot = true`) and has been bootstrapped (`cs.lastAcceptedConfiguration.isEmpty = false`);
--   - the voter's accepted state is no fresher than the node's: `j.lastAcceptedTerm < cs.lastAcceptedTerm`, or the terms are equal and `j.lastAcceptedVersion ≤ cs.lastAcceptedVersionOrMetadataVersion`;
--   - the new join votes are `(cs.joinVotes.addVote j.sourceNode).1`, and `b` is `(cs.joinVotes.addVote j.sourceNode).2`, whether the vote was new;
--   - `cs'.electionWon = cs.isElectionQuorum es cs'.joinVotes`: `electionWon` is recomputed as whether the new votes are a quorum of the last committed and of the last accepted configuration of `cs` and satisfy the strategy's additional constraint (nothing is assumed of `cs` or `es`, so a successful join may also turn `electionWon` from true to false, for instance where `cs.electionWon` disagrees with its votes, or for a strategy that is not monotone; `handleJoin_stays_won` rules this out under its hypotheses);
--   - the current term, last accepted state, local node, `startedJoinSinceLastReboot`, publish votes and `lastPublishedConfiguration` of `cs'` are those of `cs`;
--   - `cs'.lastPublishedVersion` is `cs.lastAcceptedVersion` if this join won the election (`cs'.electionWon = true` and `cs.electionWon = false`), and `cs.lastPublishedVersion` otherwise.
--
--   The Java assertion that the join targets this node (`CoordinationState.java:265`) is not checked by the transcription and does not appear here.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: CoordinationState (constructor lines 84-106, isElectionQuorum 144-154, isPublishQuorum 156-158, setInitialState 180-204, handleStartJoin 213-255, handleJoin 264-339, handleClientValue 348-407, handlePublishRequest 416-460, handlePublishResponse 471-515, handleCommit 523-573, invariant 601-611, PersistedState.markLastAcceptedStateAsCommitted 703-728, commitVotingConfiguration 730-740, VoteCollection 750-814), server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java: https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java#L64-L815; CoordinationMetadata.VotingConfiguration (lines 383-449, hasQuorum 405-409): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationMetadata.java#L383-L449; ElectionStrategy (DEFAULT_INSTANCE lines 46-59, isElectionQuorum 68-88): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L44-L110; ClusterState.getVersionOrMetadataVersion (lines 239-244): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/ClusterState.java#L239-L244; Coordinator.ZEN1_BWC_TERM (line 134): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java#L134; the messages StartJoinRequest.java, Join.java, PublishRequest.java, PublishResponse.java, ApplyCommitRequest.java in the same directory; test vectors from server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java (https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java) and CoordinationMetadataTests.java (testVotingConfiguration)

import Definitions.Def_OpenSearchCoordination

theorem OpenSearchCoordination.handleJoin_spec {V : Type} (es : ElectionStrategy) (cs : CoordinationState V) (j : Join) (cs' : CoordinationState V)
    (b : Bool) (h : cs.handleJoin es j = .ok (cs', b)) :
    j.term = cs.currentTerm ∧ cs.startedJoinSinceLastReboot = true ∧
    cs.lastAcceptedConfiguration.isEmpty = false ∧
    (j.lastAcceptedTerm < cs.lastAcceptedTerm ∨
      (j.lastAcceptedTerm = cs.lastAcceptedTerm ∧ j.lastAcceptedVersion ≤ cs.lastAcceptedVersionOrMetadataVersion)) ∧
    cs'.joinVotes = (cs.joinVotes.addVote j.sourceNode).1 ∧ b = (cs.joinVotes.addVote j.sourceNode).2 ∧
    cs'.electionWon = cs.isElectionQuorum es cs'.joinVotes ∧
    cs'.currentTerm = cs.currentTerm ∧ cs'.lastAcceptedState = cs.lastAcceptedState ∧
    cs'.localNode = cs.localNode ∧ cs'.startedJoinSinceLastReboot = cs.startedJoinSinceLastReboot ∧
    cs'.publishVotes = cs.publishVotes ∧ cs'.lastPublishedConfiguration = cs.lastPublishedConfiguration ∧
    cs'.lastPublishedVersion =
      (if cs'.electionWon = true ∧ cs.electionWon = false then cs.lastAcceptedVersion else cs.lastPublishedVersion) := by sorry
