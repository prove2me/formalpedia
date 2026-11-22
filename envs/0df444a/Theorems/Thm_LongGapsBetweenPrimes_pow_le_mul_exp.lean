-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_pow_le_mul_exp
-- name    : LongGapsBetweenPrimes.pow_le_mul_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:37:26.028735+00:00
-- url     : https://prove2.me/theorems/c5818d29-e026-4c10-be97-6f0cf92b5959
-- title:
--   Long Gaps Between Primes: pow le mul exp
-- statement:
--   Convert an additive bound into an exponential bound on powers.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L324-L333
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L324-L333

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.pow_le_mul_exp {A B t : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B)
    (ht : 0 ≤ t) (hBA : B ≤ A + t) (k : ℕ) :
    B ^ k ≤ A ^ k * Real.exp ((k : ℝ) * t) := by sorry
