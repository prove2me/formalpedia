-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_tupleAssignment_injective
-- name    : LongGapsBetweenPrimes.tupleAssignment_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:32:03.622056+00:00
-- url     : https://prove2.me/theorems/c5aff104-d156-46d6-8dd7-baef535bc8c7
-- title:
--   Long Gaps Between Primes: tuple Assignment injective
-- statement:
--   A truncated tuple is determined by its prime assignment when `P` is squarefree.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2089-L2107
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2089-L2107

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.tupleAssignment_injective {P k : ℕ} (hP : Squarefree P) (D : ℝ) :
    Function.Injective (fun r : tupleRegion P k D => tupleAssignment r.val) := by sorry
