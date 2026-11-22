-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_sieveZ_lower
-- name    : LongGapsBetweenPrimes.sieveZ_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:39.448562+00:00
-- url     : https://prove2.me/theorems/d64fdbaf-d7f9-4d02-b8f8-86dd802442f6
-- title:
--   Long Gaps Between Primes: sieve Z lower
-- statement:
--   For `x ≥ 2`, the lower sieve cutoff exceeds `x ^ 4` by at least one.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3387-L3393
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3387-L3393

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.sieveZ_lower {x : ℝ} (hx : 2 ≤ x) : x ^ 4 ≤ (sieveZ x : ℝ) - 1 := by sorry
