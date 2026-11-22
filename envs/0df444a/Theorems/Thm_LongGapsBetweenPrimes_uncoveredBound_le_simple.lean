-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_uncoveredBound_le_simple
-- name    : LongGapsBetweenPrimes.uncoveredBound_le_simple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:35.395323+00:00
-- url     : https://prove2.me/theorems/c4b25b7a-dcbb-401c-9354-944906183763
-- title:
--   Long Gaps Between Primes: uncovered Bound le simple
-- statement:
--   Bound the normalized uncovered contribution by an explicit multiple of `1 / x ^ 6`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3361-L3384
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3361-L3384

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.uncoveredBound_le_simple {n : ℕ} {M x β C : ℝ} (hx : 1 ≤ x)
    (hβ : 0 ≤ β) (hn : (n : ℝ) ≤ x) (hsize : (n : ℝ) * C ≤ x / 16)
    (hlog : 48 * Real.log x ≤ x * β) (hM : x ^ 4 ≤ M - 1) (hlogM : 1 ≤ Real.log M)
    (hgram : Real.exp (1 / x ^ 2) ≤ 5 / 4) :
    uncoveredBound n β C M (sieveD x) ≤ (5 / 4) * (2 * C ^ 2 + 2 / (Real.log 2) ^ 2) / x ^ 6 := by sorry
