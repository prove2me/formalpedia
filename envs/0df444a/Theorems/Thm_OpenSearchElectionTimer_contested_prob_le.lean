-- Prove2me | Theorems.Thm_OpenSearchElectionTimer_contested_prob_le
-- name    : OpenSearchElectionTimer.contested_prob_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T01:04:48.197303+00:00
-- url     : https://prove2.me/theorems/bc7f6db6-e340-4199-bfa7-319a6814c5cc
-- title:
--   A round of competing timers is contested with probability at most contestedBound n δ Mmin
-- statement:
--   For all natural numbers `n`, `δ`, `Mmin` with `1 ≤ n`, `1 ≤ δ` and `1 ≤ Mmin`, every `offset : Fin n → ℤ` and every `bound : Fin n → ℕ` with `Mmin ≤ bound i ≤ 2^63` for every `i`: the number of draws `x : Fin n → Fin (2^64)` with `¬ Uncontested offset bound δ x`, divided by `(2^64)^n`, is at most `contestedBound n δ Mmin = C(n, 2) · (2δ − 1) · ⌈2^63 / Mmin⌉ / 2^63`.
--
--   Among `n` candidates with arbitrary offsets and bounds at least `Mmin`, the probability that no candidate fires at least `δ` before all the others is at most about `C(n, 2) · (2δ − 1) / Mmin`. In a contested round the first candidate to fire has a follower less than `δ` behind it, and the bound is `C(n, 2)` times that of `close_pair_prob`, a union bound over the pairs. It exceeds 1, and then says nothing, when `C(n, 2) · (2δ − 1)` exceeds about `Mmin`: for `δ = 100` and `Mmin = 10000`, from `n = 11` candidates on.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: ElectionSchedulerFactory (documented delay distribution lines 71-83, settings 85-115, constructor 124-144, nonNegative 159-161, toPositiveLongAtMost 163-172, scheduleNextElection 195-241 with the bound at 203, the delay at 204 and the next attempt scheduled with the election duration as grace period at 218): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java#L62-L254; Coordinator (the scheduler built over the node's Random lines 262-263, the scheduler started after bootstrapping at 1158 and when a candidate has found a quorum of peers 1534-1550, startElectionScheduler 1567-1618 with grace period 0 at 1574, the same Random used to choose a node to abdicate to at 1818): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java; DiscoveryModule (each node's Random created as new Random(Randomness.get().nextLong()), line 213): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/discovery/DiscoveryModule.java#L213; java.util.Random (a 48-bit linear congruential generator; nextLong): https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/util/Random.html; maxDelay, nonNegative and toPositiveLongAtMost as transcribed by the OpenSearchPreVote mission

import Definitions.Def_OpenSearchElectionTimer
open OpenSearchPreVote OpenSearchElectionTimer

theorem OpenSearchElectionTimer.contested_prob_le (n δ Mmin : Nat) (hn : 1 ≤ n) (hδ : 1 ≤ δ) (hM : 1 ≤ Mmin)
    (offset : Fin n → Int) (bound : Fin n → Nat) (hbound : ∀ i, Mmin ≤ bound i ∧ bound i ≤ 2 ^ 63) :
    ((Finset.univ.filter (fun x => ¬ Uncontested offset bound δ x)).card : ℚ) / (2 ^ 64) ^ n ≤
      contestedBound n δ Mmin := by sorry
