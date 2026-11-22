-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_rpow_secant_log
-- name    : LongGapsBetweenPrimes.rpow_secant_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:31.01508+00:00
-- url     : https://prove2.me/theorems/32d7d285-3607-4c93-939e-8e431057db19
-- title:
--   Long Gaps Between Primes: rpow secant log
-- statement:
--   A secant bound controls `p ^ t - 1` using the ratio `log p / log z`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3752-L3766
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3752-L3766

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.rpow_secant_log {p z t : ℝ} (hp : 1 ≤ p) (hpz : p ≤ z) (hz : 1 < z)
    (ht : 0 ≤ t) : p ^ t - 1 ≤ (Real.log p / Real.log z) * (Real.exp (t * Real.log z) - 1) := by sorry
