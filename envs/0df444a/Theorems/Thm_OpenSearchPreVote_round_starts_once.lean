-- Prove2me | Theorems.Thm_OpenSearchPreVote_round_starts_once
-- name    : OpenSearchPreVote.round_starts_once
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:36:00.649208+00:00
-- url     : https://prove2.me/theorems/510bbec7-e5bc-47b9-a0c4-979369e4579c
-- title:
--   Once a round has started an election or been closed, it never starts one again
-- statement:
--   For every election strategy `es`, requester response `lr`, response `resp`, sender and round `r` with `r.electionStarted = true ∨ r.isClosed = true`: handling the response does not call `startElection` (`(r.handlePreVoteResponse es lr resp sender).2.1 = false`), and the resulting round again has `electionStarted = true` or `isClosed = true`. Hence, with `round_start_quorum` (after a call that calls `startElection`, the round has `electionStarted = true`) and because `close` sets `isClosed`, a round calls `startElection` at most once along any sequence of steps, and never after it is closed (Java's `compareAndSet` on `electionStarted`, PVC:272).
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: PreVoteCollector (state line 79, start 111-115, update 128-131, handlePreVoteRequest 133-163, PreVotingRound 175-300, handlePreVoteResponse 225-279, close 296-299): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/PreVoteCollector.java#L66-L301; Coordinator (updateMaxTermSeen lines 560-581, startElection 583-602, nodeMayWinElection 628-633, getPreVoteResponse 873-879, handleJoin 1267-1299, startElectionScheduler 1567-1618, the preVoteCollector.update calls 516, 653, 777, 801, 839, 1157): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java#L560-L633; ElectionSchedulerFactory (settings lines 85-115, constructor check 133-143, nonNegative 159-161, toPositiveLongAtMost 169-172, scheduleNextElection 195-241): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java#L62-L254; ElectionStrategy.isElectionQuorum (lines 68-88): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L68-L88; the messages PreVoteRequest.java and PreVoteResponse.java in the same directory; CoordinationState (handleStartJoin, handleJoin) as transcribed by the OpenSearchCoordination mission

import Definitions.Def_OpenSearchPreVote
open OpenSearchCoordination OpenSearchPreVote

theorem OpenSearchPreVote.round_starts_once {V : Type} (es : ElectionStrategy) (lr resp : PreVoteResponse)
    (sender : DiscoveryNode) (r : PreVotingRound V) (h : r.electionStarted = true ∨ r.isClosed = true) :
    (r.handlePreVoteResponse es lr resp sender).2.1 = false ∧
    ((r.handlePreVoteResponse es lr resp sender).1.electionStarted = true ∨
      (r.handlePreVoteResponse es lr resp sender).1.isClosed = true) := by sorry
