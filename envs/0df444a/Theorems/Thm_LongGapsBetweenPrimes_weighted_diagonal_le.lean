-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_weighted_diagonal_le
-- name    : LongGapsBetweenPrimes.weighted_diagonal_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:26.797801+00:00
-- url     : https://prove2.me/theorems/ce7ad12c-be38-4ca9-8a14-34ab26e53bf0
-- title:
--   Long Gaps Between Primes: weighted diagonal le
-- statement:
--   Control weighted diagonal mass by tilted and zero coefficient moments.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3060-L3083
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3060-L3083

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.weighted_diagonal_le {P k : ℕ} {D a b γ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (v : DivisorTuple P k → ℝ)
    (hv : ∀ r ∈ tupleRegion P k D, v r ^ 2 ≤ a * (tupleProduct r : ℝ) ^ γ + b) :
    (∑ r ∈ tupleRegion P k D, tupleMass r * v r ^ 2) ≤
      a * coefficientMoment P γ ^ k + b * coefficientMoment P 0 ^ k := by sorry
