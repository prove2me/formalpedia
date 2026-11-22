-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_coverLength_eq
-- name    : LongGapsBetweenPrimes.coverLength_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:06.742522+00:00
-- url     : https://prove2.me/theorems/25657391-c13f-4a9c-b067-721aad85f71d
-- title:
--   Long Gaps Between Primes: cover Length eq
-- statement:
--   The covering length is the integer part of `η * coverScale x`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4193-L4194
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4193-L4194

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.coverLength_eq (η x : ℝ) : coverLength η x = ⌊η * coverScale x⌋₊ := by sorry
