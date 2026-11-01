-- Prove2me | Theorems.Thm_OpenSearchElectionTimer_default_example
-- name    : OpenSearchElectionTimer.default_example
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T01:05:45.411139+00:00
-- url     : https://prove2.me/theorems/bcf3146f-6153-485a-91e7-9b7c897530fd
-- title:
--   The default maximum timeout: three candidates, every bound at 10 s, and a 100 ms margin
-- statement:
--   `contestedBound 3 100 10000 < 6 / 100` and `contestedBound 3 100 10000 ^ 5 < 1 / 1000000`.
--
--   With every bound at OpenSearch's default `cluster.election.max_timeout` of 10 seconds (`Mmin = 10000` milliseconds; with the default initial timeout and back-off time of 100 ms, every attempt from attempt 99 on, counting from 0, has reached it), three competing candidates and a margin of `δ = 100` milliseconds, `contested_prob_le` bounds the probability of a contested round by `contestedBound 3 100 10000 = 597 · 922337203685478 / 2^63 ≈ 0.0597`, below 6%, and `all_contested_prob_le` bounds the probability that five consecutive rounds are contested by its fifth power, about `7.6 · 10^-7`, below one in a million. The theorem itself is arithmetic on these literals. The margin of 100 ms is an illustrative choice: nothing in the model shows that it suffices for a pre-voting round and an election to complete. For earlier attempts, whose bounds are smaller, the bound is weaker: for three candidates and a 100 ms margin it is at least 1, saying nothing, whenever the smallest competing bound is at most 597 ms. The theorem itself is arithmetic on these literals. The margin of 100 ms is an illustrative choice: nothing in the model shows that it suffices for a pre-voting round and an election to complete. For earlier attempts, whose bounds are smaller, the bound is weaker: for three candidates and a 100 ms margin it is at least 1, saying nothing, whenever the smallest competing bound is at most 597 ms.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: ElectionSchedulerFactory (documented delay distribution lines 71-83, settings 85-115, constructor 124-144, nonNegative 159-161, toPositiveLongAtMost 163-172, scheduleNextElection 195-241 with the bound at 203, the delay at 204 and the next attempt scheduled with the election duration as grace period at 218): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java#L62-L254; Coordinator (the scheduler built over the node's Random lines 262-263, the scheduler started after bootstrapping at 1158 and when a candidate has found a quorum of peers 1534-1550, startElectionScheduler 1567-1618 with grace period 0 at 1574, the same Random used to choose a node to abdicate to at 1818): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java; DiscoveryModule (each node's Random created as new Random(Randomness.get().nextLong()), line 213): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/discovery/DiscoveryModule.java#L213; java.util.Random (a 48-bit linear congruential generator; nextLong): https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/util/Random.html; maxDelay, nonNegative and toPositiveLongAtMost as transcribed by the OpenSearchPreVote mission

import Definitions.Def_OpenSearchElectionTimer
open OpenSearchPreVote OpenSearchElectionTimer

theorem OpenSearchElectionTimer.default_example :
    contestedBound 3 100 10000 < 6 / 100 ∧ contestedBound 3 100 10000 ^ 5 < 1 / 1000000 := by sorry
