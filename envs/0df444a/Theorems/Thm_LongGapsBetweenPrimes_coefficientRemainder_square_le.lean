-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_coefficientRemainder_square_le
-- name    : LongGapsBetweenPrimes.coefficientRemainder_square_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:21.757669+00:00
-- url     : https://prove2.me/theorems/b39e253b-0598-4e9b-ade5-67fb753f63a6
-- title:
--   Long Gaps Between Primes: coefficient Remainder square le
-- statement:
--   Bound the squared coefficient remainder by its tail and overlap contributions.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3086-L3105
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3086-L3105

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.coefficientRemainder_square_le {P m : ℕ} {β C D M : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) (hm : m ∣ P)
    (hcut : (m : ℝ) ≤ D) (hM : 0 < M)
    (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ)) :
    coefficientRemainder P m D ^ 2 ≤
      (2 * C ^ 2 * D ^ (-(2 * β))) * (m : ℝ) ^ (2 * β) +
        2 * (4 * Real.log D / (M * Real.log 2)) ^ 2 := by sorry
