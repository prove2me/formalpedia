-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_tupleRegion_insertNth
-- name    : LongGapsBetweenPrimes.tupleRegion_insertNth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:25.87235+00:00
-- url     : https://prove2.me/theorems/922282ea-1db5-4c9c-9d04-0b142fca6912
-- title:
--   Long Gaps Between Primes: tuple Region insert Nth
-- statement:
--   Characterize truncated-region membership after inserting one divisor.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2719-L2733
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2719-L2733

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.tupleRegion_insertNth {P k : ℕ} (i : Fin (k + 1)) (d : DivisorIndex P)
    (r : DivisorTuple P k) (D : ℝ) :
    i.insertNth d r ∈ tupleRegion P (k + 1) D ↔
      r ∈ tupleRegion P k D ∧ (d.val : ℝ) ≤ D / tupleProduct r ∧
        d.val.Coprime (tupleProduct r) := by sorry
