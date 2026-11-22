-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_eulerProduct_ge_one_div_two_mul
-- name    : LongGapsBetweenPrimes.eulerProduct_ge_one_div_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:05.792462+00:00
-- url     : https://prove2.me/theorems/e8c2f770-ac42-4f1c-8424-c741d8b88aba
-- title:
--   Long Gaps Between Primes: euler Product ge one div two mul
-- statement:
--   The Euler product at `1 + t` is at least `1 / (2 * t)` when `t * log (Y + 1) ≥ 1`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1266-L1279
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1266-L1279

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.eulerProduct_ge_one_div_two_mul (Y : ℕ) {t : ℝ} (ht : 0 < t)
    (hscale : 1 ≤ t * Real.log ((Y : ℝ) + 1)) :
    1 / (2 * t) ≤ eulerProduct Y (1 + t) := by sorry
