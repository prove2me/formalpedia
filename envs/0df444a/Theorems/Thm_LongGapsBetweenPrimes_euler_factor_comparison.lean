-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_euler_factor_comparison
-- name    : LongGapsBetweenPrimes.euler_factor_comparison
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:38.953003+00:00
-- url     : https://prove2.me/theorems/add8efde-de5f-49f4-ad80-8abecf3dffb2
-- title:
--   Long Gaps Between Primes: euler factor comparison
-- statement:
--   Compare an Euler factor at exponent one with its shift by `r`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1045-L1074
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1045-L1074

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.euler_factor_comparison {p r : ℝ} (hp : 2 ≤ p) (hr : 0 ≤ r) :
    (1 - p ^ (-(1 : ℝ)))⁻¹ ≤
      (1 - p ^ (-(1 + r)))⁻¹ * Real.exp (2 * r * Real.log p / p) := by sorry
