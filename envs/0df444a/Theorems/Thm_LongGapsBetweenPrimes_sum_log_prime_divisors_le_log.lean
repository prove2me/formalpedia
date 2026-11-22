-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_sum_log_prime_divisors_le_log
-- name    : LongGapsBetweenPrimes.sum_log_prime_divisors_le_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:23.442364+00:00
-- url     : https://prove2.me/theorems/934ffadb-9ac7-4b34-8e05-d27079825b15
-- title:
--   Long Gaps Between Primes: sum log prime divisors le log
-- statement:
--   The logarithms of distinct prime divisors sum to at most `log n`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L906-L919
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L906-L919

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.sum_log_prime_divisors_le_log {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (∑ p ∈ N.primesLE, if p ∣ n then Real.log p else 0) ≤ Real.log n := by sorry
