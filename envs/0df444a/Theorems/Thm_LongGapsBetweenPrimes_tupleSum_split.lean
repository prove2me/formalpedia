-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_tupleSum_split
-- name    : LongGapsBetweenPrimes.tupleSum_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:27.122339+00:00
-- url     : https://prove2.me/theorems/acddcc07-7600-4cf7-b17c-f45c3ff85835
-- title:
--   Long Gaps Between Primes: tuple Sum split
-- statement:
--   Split a truncated tuple sum by one coordinate.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2736-L2750
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2736-L2750

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.tupleSum_split {P k : ℕ} (i : Fin (k + 1)) (D : ℝ)
    (G : Fin (k + 1) → DivisorIndex P → ℝ) :
    (∑ r ∈ tupleRegion P (k + 1) D, ∏ j, G j (r j)) =
      ∑ r ∈ tupleRegion P k D,
        (∑ d : DivisorIndex P,
          if (d.val : ℝ) ≤ D / tupleProduct r ∧ d.val.Coprime (tupleProduct r) then G i d else 0) *
          ∏ j, G (i.succAbove j) (r j) := by sorry
