-- Prove2me | Theorems.Thm_OAI_PiExponent_rational_approximation_lower_bound
-- name    : OAI.PiExponent.rational_approximation_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-12T19:39:38.115863+00:00
-- url     : https://prove2.me/theorems/81b8b965-2fac-45fd-b489-f9cac3c04233
-- title:
--   Uniform lower bound for all integer numerators
-- statement:
--   For every real exponent nu greater than 2, there is a threshold Q at least 2 such that for every natural denominator q at least Q and every integer numerator p, the distance between pi and p/q is at least q to the power -nu.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

theorem OAI.PiExponent.rational_approximation_lower_bound (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ (p : ℤ) (q : ℕ), Q ≤ q →
        (q : ℝ) ^ (-nu) ≤ |Real.pi - (p : ℝ) / (q : ℝ)| := by
  sorry
