-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_euler_factor_left_comparison
-- name    : LongGapsBetweenPrimes.euler_factor_left_comparison
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:23.22686+00:00
-- url     : https://prove2.me/theorems/cb22ae88-6ffa-4528-847b-b5c62781983a
-- title:
--   Long Gaps Between Primes: euler factor left comparison
-- statement:
--   Bound the cost of shifting an Euler factor to exponent `1 - t`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3692-L3730
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3692-L3730

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.euler_factor_left_comparison {p t : ℝ} (hp : 2 ≤ p) (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    (1 - p ^ (-(1 - t)))⁻¹ ≤ (1 - p ^ (-(1 : ℝ)))⁻¹ *
      Real.exp (smoothEulerConstant * (p ^ t - 1) / p) := by sorry
