-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_homogeneous_coordinate_power_sum_mem
-- name    : OAI.PiExponent.FormalInterpolation.homogeneous_coordinate_power_sum_mem
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:55:44.5497+00:00
-- url     : https://prove2.me/theorems/0df818d2-55c0-4d92-b566-d1805c522269
-- title:
--   Homogeneity separates a sum of coordinate powers
-- statement:
--   For positive rational variable weights and generators homogeneous of the same positive degree, membership of a finite sum of scalar multiples of distinct powers of one coordinate in the generated ideal implies membership of each summand. Prove this by showing the generated ideal is graded and projecting to the distinct weighted degrees `n * w i`; strict positivity ensures those degrees are distinct.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.homogeneous_coordinate_power_sum_mem
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (i : Fin d) (K : Nat) (c : Fin (K + 1) → ℂ)
    (hsum : (∑ n : Fin (K + 1), MvPolynomial.C (c n) *
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ (n : Nat)) ∈
      Ideal.span (Set.range p)) :
    ∀ n : Fin (K + 1), MvPolynomial.C (c n) *
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ (n : Nat) ∈
      Ideal.span (Set.range p) := by sorry
