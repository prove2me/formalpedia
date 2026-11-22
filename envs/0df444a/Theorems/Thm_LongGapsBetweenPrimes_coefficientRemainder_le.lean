-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_coefficientRemainder_le
-- name    : LongGapsBetweenPrimes.coefficientRemainder_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:09.491086+00:00
-- url     : https://prove2.me/theorems/5ae5f2a8-7337-4522-8af4-123725087b75
-- title:
--   Long Gaps Between Primes: coefficient Remainder le
-- statement:
--   Bound the coefficient remainder by a power tail and an error from shared primes.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2950-L2972
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2950-L2972

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.coefficientRemainder_le {P m : ℕ} {β C D M : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) (hm : m ∣ P)
    (hcut : (m : ℝ) ≤ D) (hM : 0 < M)
    (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ)) :
    coefficientRemainder P m D ≤ C * ((m : ℝ) / D) ^ β +
      4 * Real.log D / (M * Real.log 2) := by sorry
