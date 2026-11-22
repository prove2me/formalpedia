-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_abs_residueFactor_le_one
-- name    : LongGapsBetweenPrimes.abs_residueFactor_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:09.820798+00:00
-- url     : https://prove2.me/theorems/0bde6cd6-b034-4d00-b2ae-ba16531ba2f4
-- title:
--   Long Gaps Between Primes: abs residue Factor le one
-- statement:
--   Every residue factor has absolute value at most one.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2596-L2603
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2596-L2603

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.abs_residueFactor_le_one {p : ℕ} (hp : 1 < p) (a t : Fin p) :
    |residueFactor a t| ≤ 1 := by sorry
