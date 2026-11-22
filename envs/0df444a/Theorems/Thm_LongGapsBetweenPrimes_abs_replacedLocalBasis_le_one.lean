-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_abs_replacedLocalBasis_le_one
-- name    : LongGapsBetweenPrimes.abs_replacedLocalBasis_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:43.268828+00:00
-- url     : https://prove2.me/theorems/1eef3810-09c0-4b32-90cb-104a2020a1cf
-- title:
--   Long Gaps Between Primes: abs replaced Local Basis le one
-- statement:
--   Every replaced local basis value has absolute value at most one.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3145-L3156
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3145-L3156

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.abs_replacedLocalBasis_le_one {p k : ℕ} (hp : 1 < p)
    (root : Fin k → Fin p) (i : Fin k) (j : Option (Fin k)) (t : Fin p) :
    |replacedLocalBasis root i j t| ≤ 1 := by sorry
