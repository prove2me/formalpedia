-- Prove2me | Theorems.Thm_OAI_PiExponent_rational_approximation_local_bound
-- name    : OAI.PiExponent.rational_approximation_local_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-12T19:43:20.984668+00:00
-- url     : https://prove2.me/theorems/126b5555-882f-427c-8ae9-e383ea1a85f3
-- title:
--   Approximation bound for numerators in a bounded range
-- statement:
--   For every real exponent nu greater than 2, there is a threshold Q such that the desired lower bound holds for all denominators q at least Q and numerators p satisfying |p| ≤ 4q.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

theorem OAI.PiExponent.rational_approximation_local_bound (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ (p : ℤ) (q : ℕ), Q ≤ q → |(p : ℝ)| ≤ 4 * (q : ℝ) →
        (q : ℝ) ^ (-nu) ≤ |Real.pi - (p : ℝ) / (q : ℝ)| := by sorry
