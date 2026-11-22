-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_sum_primeFactors_inv_le
-- name    : LongGapsBetweenPrimes.sum_primeFactors_inv_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:51.838526+00:00
-- url     : https://prove2.me/theorems/868921fc-5545-4c13-8346-120812f8e797
-- title:
--   Long Gaps Between Primes: sum prime Factors inv le
-- statement:
--   A lower bound on prime factors controls their reciprocal sum using `log m`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2878-L2904
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2878-L2904

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.sum_primeFactors_inv_le {P m : ℕ} (hP : Squarefree P) (hm : m ∣ P)
    {M : ℝ} (hM : 0 < M) (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ)) :
    (∑ p ∈ m.primeFactors, 4 / (p : ℝ)) ≤ 4 * Real.log m / (M * Real.log 2) := by sorry
