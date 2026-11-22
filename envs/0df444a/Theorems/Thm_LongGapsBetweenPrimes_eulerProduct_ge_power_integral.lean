-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_eulerProduct_ge_power_integral
-- name    : LongGapsBetweenPrimes.eulerProduct_ge_power_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:06.806482+00:00
-- url     : https://prove2.me/theorems/d406d26b-8190-474e-847c-003cdbdb20a1
-- title:
--   Long Gaps Between Primes: euler Product ge power integral
-- statement:
--   Bound the Euler product below by an integral of a negative power.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1245-L1263
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1245-L1263

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.eulerProduct_ge_power_integral (Y : ℕ) {t : ℝ} (ht : 0 < t) :
    (1 - ((Y : ℝ) + 1) ^ (-t)) / t ≤ eulerProduct Y (1 + t) := by sorry
