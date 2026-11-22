-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_abs_rawLocalBasis_le_one
-- name    : LongGapsBetweenPrimes.abs_rawLocalBasis_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:47.314803+00:00
-- url     : https://prove2.me/theorems/cd9cf173-ac50-449c-afb0-d9adec5e1069
-- title:
--   Long Gaps Between Primes: abs raw Local Basis le one
-- statement:
--   Every unnormalized local basis value has absolute value at most one.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2606-L2610
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2606-L2610

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.abs_rawLocalBasis_le_one {p k : ℕ} (hp : 1 < p) (root : Fin k → Fin p)
    (i : Option (Fin k)) (t : Fin p) : |rawLocalBasis root i t| ≤ 1 := by sorry
