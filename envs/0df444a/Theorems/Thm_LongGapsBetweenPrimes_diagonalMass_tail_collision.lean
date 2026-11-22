-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_diagonalMass_tail_collision
-- name    : LongGapsBetweenPrimes.diagonalMass_tail_collision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:41:54.732648+00:00
-- url     : https://prove2.me/theorems/65e495ee-aea3-47c0-9f23-3309a34909ca
-- title:
--   Long Gaps Between Primes: diagonal Mass tail collision
-- statement:
--   The only losses in the diagonal are the product cutoff and shared primes.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1994-L2013
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1994-L2013

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.diagonalMass_tail_collision {P M k : ℕ} {β C D : ℝ}
    (h : CoefficientEstimates P β C) (hM : 0 < M)
    (hmin : ∀ p ∈ P.primeFactors, M < p) (hD : 0 < D) (hβ : 0 ≤ β) :
    coefficientMoment P 0 ^ k - diagonalMass P k D ≤
      D ^ (-β) * coefficientMoment P β ^ k +
        (16 * (k : ℝ) ^ 2 / M) * coefficientMoment P 0 ^ k := by sorry
