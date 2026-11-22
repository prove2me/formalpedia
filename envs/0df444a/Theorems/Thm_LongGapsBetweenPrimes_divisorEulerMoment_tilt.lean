-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_divisorEulerMoment_tilt
-- name    : LongGapsBetweenPrimes.divisorEulerMoment_tilt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:52.337958+00:00
-- url     : https://prove2.me/theorems/198747dc-9bc0-4754-a8a5-0ab13f4ff0e3
-- title:
--   Long Gaps Between Primes: divisor Euler Moment tilt
-- statement:
--   Tilting a squarefree divisor moment costs an exponential factor.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1512-L1530
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1512-L1530

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.divisorEulerMoment_tilt (ps : Finset ℕ) (hps : ∀ p ∈ ps, p.Prime)
    {γ E : ℝ} (hγ : 0 ≤ γ) (hE : ∀ p ∈ ps, (p : ℝ) ^ γ ≤ E) :
    divisorEulerMoment (∏ p ∈ ps, p) γ ≤
      divisorEulerMoment (∏ p ∈ ps, p) 0 *
        Real.exp (E * γ * ∑ p ∈ ps, Real.log p / p) := by sorry
