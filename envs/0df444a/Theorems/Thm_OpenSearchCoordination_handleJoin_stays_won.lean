-- Prove2me | Theorems.Thm_OpenSearchCoordination_handleJoin_stays_won
-- name    : OpenSearchCoordination.handleJoin_stays_won
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:33:32.748193+00:00
-- url     : https://prove2.me/theorems/f1105082-e437-473d-bd6b-4d84ddeb24dc
-- title:
--   A won election stays won (CoordinationState.java:323-324)
-- statement:
--   Let `es` be a monotone election strategy (`es.Monotone`) and `cs` a coordination state whose `electionWon` agrees with the election-quorum status of its join votes, `cs.electionWon = cs.isElectionQuorum es cs.joinVotes` (the second assertion of `invariant()`). If `cs.electionWon = true` and `cs.handleJoin es j = .ok (cs', b)`, then `cs'.electionWon = true`.
--
--   This is the assertion `assert !prevElectionWon || electionWon` ("we cannot go from won to not won") in `handleJoin`: a join only adds a vote, a superset of a quorum is a quorum, and a monotone strategy's constraint survives added votes. Java does not require plugin strategies to be monotone; the theorem does.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: CoordinationState (constructor lines 84-106, isElectionQuorum 144-154, isPublishQuorum 156-158, setInitialState 180-204, handleStartJoin 213-255, handleJoin 264-339, handleClientValue 348-407, handlePublishRequest 416-460, handlePublishResponse 471-515, handleCommit 523-573, invariant 601-611, PersistedState.markLastAcceptedStateAsCommitted 703-728, commitVotingConfiguration 730-740, VoteCollection 750-814), server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java: https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java#L64-L815; CoordinationMetadata.VotingConfiguration (lines 383-449, hasQuorum 405-409): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationMetadata.java#L383-L449; ElectionStrategy (DEFAULT_INSTANCE lines 46-59, isElectionQuorum 68-88): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L44-L110; ClusterState.getVersionOrMetadataVersion (lines 239-244): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/ClusterState.java#L239-L244; Coordinator.ZEN1_BWC_TERM (line 134): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java#L134; the messages StartJoinRequest.java, Join.java, PublishRequest.java, PublishResponse.java, ApplyCommitRequest.java in the same directory; test vectors from server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java (https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java) and CoordinationMetadataTests.java (testVotingConfiguration)

import Definitions.Def_OpenSearchCoordination

theorem OpenSearchCoordination.handleJoin_stays_won {V : Type} (es : ElectionStrategy) (hes : es.Monotone) (cs : CoordinationState V) (j : Join)
    (cs' : CoordinationState V) (b : Bool) (hinv : cs.electionWon = cs.isElectionQuorum es cs.joinVotes)
    (h : cs.handleJoin es j = .ok (cs', b)) (hw : cs.electionWon = true) : cs'.electionWon = true := by sorry
