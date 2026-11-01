-- Prove2me | Theorems.Thm_OpenSearchElectionTimer_all_contested_prob_le
-- name    : OpenSearchElectionTimer.all_contested_prob_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T01:05:14.473048+00:00
-- url     : https://prove2.me/theorems/2dd0fa6b-10f3-46ab-8924-185424d1eda3
-- title:
--   Repeated contests become exponentially unlikely once the per-round bound is below 1, even against an adaptive scheduler
-- statement:
--   For all natural numbers `n`, `K`, `δ`, `Mmin` with `1 ≤ n`, `1 ≤ δ` and `1 ≤ Mmin`, and all functions `offset : Fin K → (Fin K → Fin n → Fin (2^64)) → Fin n → ℤ` and `bound : Fin K → (Fin K → Fin n → Fin (2^64)) → Fin n → ℕ` (the offsets and bounds of round `k` for candidate `i`, given the draw `X` of all `K` rounds) such that
--
--   - every bound lies between `Mmin` and `2^63`: `Mmin ≤ bound k X i ≤ 2^63` for all `k`, `X` and `i`;
--   - the offsets and bounds of round `k` depend only on the draws of the earlier rounds: for all `k`, `X` and `X'`, if `X m = X' m` for every `m < k`, then `offset k X = offset k X'` and `bound k X = bound k X'`;
--
--   the number of draws `X : Fin K → Fin n → Fin (2^64)` such that every round is contested, `¬ Uncontested (offset k X) (bound k X) δ (X k)` for every `k : Fin K`, divided by `(2^64)^(n K)`, is at most `contestedBound n δ Mmin ^ K`.
--
--   An adversary that schedules the network, choosing deterministically when each candidate's timer of round `k` starts and with which bound, in reaction to everything drawn in the earlier rounds but not to the draws of round `k` or later, cannot make `K` rounds of the same `n` candidates (each drawing afresh in every round) all contested with probability above `contestedBound n δ Mmin ^ K`. That bound decreases exponentially in `K` when `contestedBound n δ Mmin < 1` and says nothing otherwise.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: ElectionSchedulerFactory (documented delay distribution lines 71-83, settings 85-115, constructor 124-144, nonNegative 159-161, toPositiveLongAtMost 163-172, scheduleNextElection 195-241 with the bound at 203, the delay at 204 and the next attempt scheduled with the election duration as grace period at 218): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java#L62-L254; Coordinator (the scheduler built over the node's Random lines 262-263, the scheduler started after bootstrapping at 1158 and when a candidate has found a quorum of peers 1534-1550, startElectionScheduler 1567-1618 with grace period 0 at 1574, the same Random used to choose a node to abdicate to at 1818): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java; DiscoveryModule (each node's Random created as new Random(Randomness.get().nextLong()), line 213): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/discovery/DiscoveryModule.java#L213; java.util.Random (a 48-bit linear congruential generator; nextLong): https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/util/Random.html; maxDelay, nonNegative and toPositiveLongAtMost as transcribed by the OpenSearchPreVote mission

import Definitions.Def_OpenSearchElectionTimer
open OpenSearchPreVote OpenSearchElectionTimer

theorem OpenSearchElectionTimer.all_contested_prob_le (n K δ Mmin : Nat) (hn : 1 ≤ n) (hδ : 1 ≤ δ) (hM : 1 ≤ Mmin)
    (offset : Fin K → (Fin K → Fin n → Fin (2 ^ 64)) → Fin n → Int)
    (bound : Fin K → (Fin K → Fin n → Fin (2 ^ 64)) → Fin n → Nat)
    (hbound : ∀ k X i, Mmin ≤ bound k X i ∧ bound k X i ≤ 2 ^ 63)
    (hcausal : ∀ k X X', (∀ m : Fin K, m < k → X m = X' m) → offset k X = offset k X' ∧ bound k X = bound k X') :
    ((Finset.univ.filter (fun X : Fin K → Fin n → Fin (2 ^ 64) =>
        ∀ k, ¬ Uncontested (offset k X) (bound k X) δ (X k))).card : ℚ) / (2 ^ 64) ^ (n * K) ≤
      contestedBound n δ Mmin ^ K := by sorry
