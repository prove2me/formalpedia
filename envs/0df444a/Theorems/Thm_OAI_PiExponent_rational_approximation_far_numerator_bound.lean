-- Prove2me | Theorems.Thm_OAI_PiExponent_rational_approximation_far_numerator_bound
-- name    : OAI.PiExponent.rational_approximation_far_numerator_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-12T19:43:28.278988+00:00
-- url     : https://prove2.me/theorems/8d686522-5d95-4efc-a654-c365c23fb131
-- title:
--   Approximation bound for large numerators
-- statement:
--   For every exponent nu greater than 2, denominator q at least 2, and integer numerator p with |p| greater than 4q, the desired lower bound holds.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

theorem OAI.PiExponent.rational_approximation_far_numerator_bound (nu : ℝ) (hnu : 2 < nu)
    (p : ℤ) (q : ℕ) (hq : 2 ≤ q) (hlarge : 4 * (q : ℝ) < |(p : ℝ)|) :
    (q : ℝ) ^ (-nu) ≤ |Real.pi - (p : ℝ) / (q : ℝ)| := by sorry
