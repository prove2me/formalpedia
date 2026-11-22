-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_exp_neg_nat_mul_log
-- name    : LongGapsBetweenPrimes.exp_neg_nat_mul_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:32:02.858314+00:00
-- url     : https://prove2.me/theorems/09df5d2e-3a99-4727-8fc8-56cc5fe8dfb1
-- title:
--   Long Gaps Between Primes: exp neg nat mul log
-- statement:
--   Rewrite `exp (-n * log x)` as `1 / x ^ n`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3305-L3307
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3305-L3307

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.exp_neg_nat_mul_log {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.exp (-(n : ℝ) * Real.log x) = 1 / x ^ n := by sorry
