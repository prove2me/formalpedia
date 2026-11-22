-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_coverW_large
-- name    : LongGapsBetweenPrimes.coverW_large
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:00.808798+00:00
-- url     : https://prove2.me/theorems/5dbc98ef-da44-4fb1-bad7-10575b0af71e
-- title:
--   Long Gaps Between Primes: cover W large
-- statement:
--   The small-prime cutoff exceeds `2 * (log x)^2`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4136-L4139
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4136-L4139

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.coverW_large {x : ℝ} (hL : 2 ≤ Real.log x) :
    2 * Real.log x ^ 2 < (coverW x : ℝ) := by sorry
