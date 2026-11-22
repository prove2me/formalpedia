-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_integral_exp_decay_le
-- name    : LongGapsBetweenPrimes.integral_exp_decay_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:19.439087+00:00
-- url     : https://prove2.me/theorems/e5afee0f-226b-46da-b402-661f07385c03
-- title:
--   Long Gaps Between Primes: integral exp decay le
-- statement:
--   An exponential decay integral starting at a nonnegative point is at most `1 / L`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1313-L1319
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1313-L1319

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.integral_exp_decay_le {L a : ℝ} (hL : 0 < L) (ha : 0 ≤ a) (b : ℝ) :
    (∫ t : ℝ in a..b, Real.exp (-L * t)) ≤ 1 / L := by sorry
