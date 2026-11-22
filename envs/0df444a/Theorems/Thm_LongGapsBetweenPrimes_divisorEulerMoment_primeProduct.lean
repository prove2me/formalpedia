-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_divisorEulerMoment_primeProduct
-- name    : LongGapsBetweenPrimes.divisorEulerMoment_primeProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:31:16.621833+00:00
-- url     : https://prove2.me/theorems/8fe7a866-45df-41c0-a89f-6fb1f4d3dd79
-- title:
--   Long Gaps Between Primes: divisor Euler Moment prime Product
-- statement:
--   Factor the divisor Euler moment of a product of distinct primes.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1130-L1157
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1130-L1157

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.divisorEulerMoment_primeProduct (ps : Finset ℕ) (hps : ∀ p ∈ ps, p.Prime) (γ : ℝ) :
    divisorEulerMoment (∏ p ∈ ps, p) γ =
      ∏ p ∈ ps, (1 + (p : ℝ) ^ γ / ((p : ℝ) - 1)) := by sorry
