-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_sum_prime_log_div_le
-- name    : LongGapsBetweenPrimes.sum_prime_log_div_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:31:12.449806+00:00
-- url     : https://prove2.me/theorems/400d4299-c7e3-462f-834c-ba0928dc3ef1
-- title:
--   Long Gaps Between Primes: sum prime log div le
-- statement:
--   An elementary upper bound for the logarithmically weighted prime harmonic sum.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L922-L962
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L922-L962

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.sum_prime_log_div_le {N : ℕ} (hN : 1 ≤ N) :
    (∑ p ∈ N.primesLE, Real.log p / p) ≤ Real.log N + Real.log 4 := by sorry
