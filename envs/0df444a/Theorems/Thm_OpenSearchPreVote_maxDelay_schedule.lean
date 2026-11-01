-- Prove2me | Theorems.Thm_OpenSearchPreVote_maxDelay_schedule
-- name    : OpenSearchPreVote.maxDelay_schedule
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:36:36.133567+00:00
-- url     : https://prove2.me/theorems/f75d4dd1-7526-4870-86f8-b961eac892c5
-- title:
--   The delay bound backs off linearly from the initial timeout to the maximum timeout
-- statement:
--   For valid scheduler settings `s`:
--
--   - `maxDelay s 0 = s.initialTimeout`;
--   - `maxDelay s k ≤ maxDelay s k'` whenever `k ≤ k'`;
--   - for every `k` with `maxDelay s k < s.maxTimeout`, `maxDelay s (k + 1)` is `maxDelay s k + s.backoffTime` or `s.maxTimeout`;
--   - `maxDelay s k = s.maxTimeout` for every `k ≥ s.maxTimeout` (the number `maxTimeout` used as an attempt count: since `backoffTime ≥ 1`, the bound has reached the maximum by then).
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: PreVoteCollector (state line 79, start 111-115, update 128-131, handlePreVoteRequest 133-163, PreVotingRound 175-300, handlePreVoteResponse 225-279, close 296-299): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/PreVoteCollector.java#L66-L301; Coordinator (updateMaxTermSeen lines 560-581, startElection 583-602, nodeMayWinElection 628-633, getPreVoteResponse 873-879, handleJoin 1267-1299, startElectionScheduler 1567-1618, the preVoteCollector.update calls 516, 653, 777, 801, 839, 1157): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java#L560-L633; ElectionSchedulerFactory (settings lines 85-115, constructor check 133-143, nonNegative 159-161, toPositiveLongAtMost 169-172, scheduleNextElection 195-241): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java#L62-L254; ElectionStrategy.isElectionQuorum (lines 68-88): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L68-L88; the messages PreVoteRequest.java and PreVoteResponse.java in the same directory; CoordinationState (handleStartJoin, handleJoin) as transcribed by the OpenSearchCoordination mission

import Definitions.Def_OpenSearchPreVote
open OpenSearchCoordination OpenSearchPreVote

theorem OpenSearchPreVote.maxDelay_schedule (s : SchedulerSettings) (hs : s.Valid) :
    maxDelay s 0 = s.initialTimeout ∧ (∀ k k', k ≤ k' → maxDelay s k ≤ maxDelay s k') ∧
    (∀ k, maxDelay s k < s.maxTimeout → maxDelay s (k + 1) = maxDelay s k + s.backoffTime ∨
      maxDelay s (k + 1) = s.maxTimeout) ∧
    ∀ k, s.maxTimeout ≤ k → maxDelay s k = s.maxTimeout := by sorry
