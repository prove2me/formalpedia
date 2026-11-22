-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_diagonalMass_normalized_lower
-- name    : LongGapsBetweenPrimes.diagonalMass_normalized_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:59.617251+00:00
-- url     : https://prove2.me/theorems/fcdc3ef6-0ced-4aa6-8503-9d0e1435aeb2
-- title:
--   Long Gaps Between Primes: diagonal Mass normalized lower
-- statement:
--   The normalized diagonal mass loses only a power tail and prime collisions.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3241-L3251
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3241-L3251

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.diagonalMass_normalized_lower {P M k : ℕ} {β C D : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) (hD : 0 < D)
    (hM : 0 < M) (hmin : ∀ p ∈ P.primeFactors, M < p) :
    (1 - (D ^ (-β) * Real.exp ((k : ℝ) * C * β) + 16 * (k : ℝ) ^ 2 / M)) *
      coefficientMoment P 0 ^ k ≤ diagonalMass P k D := by sorry
