-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_gramBound_le_simple
-- name    : LongGapsBetweenPrimes.gramBound_le_simple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:39.337+00:00
-- url     : https://prove2.me/theorems/468aa701-6bd7-4dae-ab7d-6d4b1964779e
-- title:
--   Long Gaps Between Primes: gram Bound le simple
-- statement:
--   Bound the Gram factor by `exp (1 / x ^ 2)`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3328-L3340
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3328-L3340

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.gramBound_le_simple {n : ℕ} {M x : ℝ} (hx : 1 ≤ x) (hn : (n : ℝ) ≤ x)
    (hM : x ^ 4 ≤ M - 1) (hlog : 1 ≤ Real.log M) :
    gramBound n M (sieveD x) ≤ Real.exp (1 / x ^ 2) := by sorry
