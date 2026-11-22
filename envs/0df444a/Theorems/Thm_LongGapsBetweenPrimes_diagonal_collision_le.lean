-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_diagonal_collision_le
-- name    : LongGapsBetweenPrimes.diagonal_collision_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:41:44.780508+00:00
-- url     : https://prove2.me/theorems/c9734dbd-7648-4980-af99-ec82fe5c46d1
-- title:
--   Long Gaps Between Primes: diagonal collision le
-- statement:
--   The discarded mass from tuples sharing a prime, with an explicit constant.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1923-L1984
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1923-L1984

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.diagonal_collision_le {P M k : ℕ} {β C : ℝ}
    (h : CoefficientEstimates P β C) (hM : 0 < M)
    (hmin : ∀ p ∈ P.primeFactors, M < p) :
    (∑ r : DivisorTuple P k, tupleMass r *
      if ¬∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val then 1 else 0) ≤
        (16 * (k : ℝ) ^ 2 / M) * coefficientMoment P 0 ^ k := by sorry
