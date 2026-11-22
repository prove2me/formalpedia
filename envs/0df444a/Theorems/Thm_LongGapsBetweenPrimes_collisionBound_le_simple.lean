-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_collisionBound_le_simple
-- name    : LongGapsBetweenPrimes.collisionBound_le_simple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:36.587808+00:00
-- url     : https://prove2.me/theorems/a5494387-4f9d-422b-a850-ff3bc384f749
-- title:
--   Long Gaps Between Primes: collision Bound le simple
-- statement:
--   The collision contribution is at most `16 / x ^ 2`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3343-L3348
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3343-L3348

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.collisionBound_le_simple {n : ℕ} {M x : ℝ} (hx : 0 < x)
    (hn : (n : ℝ) ≤ x) (hM : x ^ 4 ≤ M) :
    16 * (n : ℝ) ^ 2 / M ≤ 16 / x ^ 2 := by sorry
