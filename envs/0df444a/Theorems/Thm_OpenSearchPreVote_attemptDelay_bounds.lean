-- Prove2me | Theorems.Thm_OpenSearchPreVote_attemptDelay_bounds
-- name    : OpenSearchPreVote.attemptDelay_bounds
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:36:27.72178+00:00
-- url     : https://prove2.me/theorems/df632a13-43e1-470f-9f96-ddadd0cb16bd
-- title:
--   Every election attempt waits between one millisecond and its bound, after the grace period
-- statement:
--   For valid scheduler settings `s` (`s.Valid`), every attempt number `k`, every drawn random number `r` (any integer) and every grace period `g`: `1 ≤ maxDelay s k`, and `g + 1 ≤ attemptDelay s k r g ≤ g + maxDelay s k`. With `maxDelay s k = min(maxTimeout, initialTimeout + k · backoffTime)` and `attemptDelay s k r g = (nonNegative r mod maxDelay s k) + 1 + g`, this is the range `(0, maxDelay]` of the scheduler's documentation (ESF:71-83) shifted by the grace period, and the assertion `0 < upperBound` of `toPositiveLongAtMost` (ESF:170) always holds.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: PreVoteCollector (state line 79, start 111-115, update 128-131, handlePreVoteRequest 133-163, PreVotingRound 175-300, handlePreVoteResponse 225-279, close 296-299): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/PreVoteCollector.java#L66-L301; Coordinator (updateMaxTermSeen lines 560-581, startElection 583-602, nodeMayWinElection 628-633, getPreVoteResponse 873-879, handleJoin 1267-1299, startElectionScheduler 1567-1618, the preVoteCollector.update calls 516, 653, 777, 801, 839, 1157): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java#L560-L633; ElectionSchedulerFactory (settings lines 85-115, constructor check 133-143, nonNegative 159-161, toPositiveLongAtMost 169-172, scheduleNextElection 195-241): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java#L62-L254; ElectionStrategy.isElectionQuorum (lines 68-88): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L68-L88; the messages PreVoteRequest.java and PreVoteResponse.java in the same directory; CoordinationState (handleStartJoin, handleJoin) as transcribed by the OpenSearchCoordination mission

import Definitions.Def_OpenSearchPreVote
open OpenSearchCoordination OpenSearchPreVote

theorem OpenSearchPreVote.attemptDelay_bounds (s : SchedulerSettings) (hs : s.Valid) (k : Nat) (r : Int)
    (g : Nat) :
    1 ≤ maxDelay s k ∧ g + 1 ≤ attemptDelay s k r g ∧ attemptDelay s k r g ≤ g + maxDelay s k := by sorry
