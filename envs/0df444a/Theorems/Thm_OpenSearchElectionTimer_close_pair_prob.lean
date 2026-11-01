-- Prove2me | Theorems.Thm_OpenSearchElectionTimer_close_pair_prob
-- name    : OpenSearchElectionTimer.close_pair_prob
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T01:04:18.51595+00:00
-- url     : https://prove2.me/theorems/d46c5c14-b5e3-4289-ac94-a0a3824e7cfb
-- title:
--   Two timers fire less than δ apart with probability at most about (2δ − 1)/Mmin
-- statement:
--   For all integers `a`, `b` and natural numbers `Ma`, `Mb`, `Mmin`, `δ` with `1 ≤ Mmin`, `Mmin ≤ Mb ≤ 2^63` and `1 ≤ δ`: the number of pairs of draws `(x, y) : Fin (2^64) × Fin (2^64)` with `|(a + randomDelay Ma x) − (b + randomDelay Mb y)| < δ`, divided by `(2^64)^2`, is at most `(2δ − 1) · ⌈2^63 / Mmin⌉ / 2^63`, where `2δ − 1` is computed in the natural numbers and `⌈2^63 / Mmin⌉ = (2^63 + Mmin − 1) / Mmin`.
--
--   Two candidates with offsets `a` and `b` and independent uniform draws fire less than `δ` milliseconds apart with probability at most about `(2δ − 1) / Mmin`, whatever the offsets and whatever the first candidate's bound `Ma`, on which nothing is assumed: for each value of the first draw, the second delay must fall among the `2δ − 1` integers less than `δ` away from a fixed point. With `δ = 100` and `Mmin = 10000` the bound is about 1.99%.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: ElectionSchedulerFactory (documented delay distribution lines 71-83, settings 85-115, constructor 124-144, nonNegative 159-161, toPositiveLongAtMost 163-172, scheduleNextElection 195-241 with the bound at 203, the delay at 204 and the next attempt scheduled with the election duration as grace period at 218): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java#L62-L254; Coordinator (the scheduler built over the node's Random lines 262-263, the scheduler started after bootstrapping at 1158 and when a candidate has found a quorum of peers 1534-1550, startElectionScheduler 1567-1618 with grace period 0 at 1574, the same Random used to choose a node to abdicate to at 1818): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java; DiscoveryModule (each node's Random created as new Random(Randomness.get().nextLong()), line 213): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/discovery/DiscoveryModule.java#L213; java.util.Random (a 48-bit linear congruential generator; nextLong): https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/util/Random.html; maxDelay, nonNegative and toPositiveLongAtMost as transcribed by the OpenSearchPreVote mission

import Definitions.Def_OpenSearchElectionTimer
open OpenSearchPreVote OpenSearchElectionTimer

theorem OpenSearchElectionTimer.close_pair_prob (a b : Int) (Ma Mb Mmin δ : Nat) (hM : 1 ≤ Mmin)
    (hMb : Mmin ≤ Mb ∧ Mb ≤ 2 ^ 63) (hδ : 1 ≤ δ) :
    ((Finset.univ.filter (fun p : Fin (2 ^ 64) × Fin (2 ^ 64) =>
        |(a + randomDelay Ma p.1) - (b + randomDelay Mb p.2)| < δ)).card : ℚ) / (2 ^ 64) ^ 2 ≤
      (2 * δ - 1 : ℕ) * ((2 ^ 63 + Mmin - 1) / Mmin : ℕ) / 2 ^ 63 := by sorry
