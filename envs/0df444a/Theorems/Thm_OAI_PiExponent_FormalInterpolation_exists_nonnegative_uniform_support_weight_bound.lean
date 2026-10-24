-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_exists_nonnegative_uniform_support_weight_bound
-- name    : OAI.PiExponent.FormalInterpolation.exists_nonnegative_uniform_support_weight_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:07:14.344339+00:00
-- url     : https://prove2.me/theorems/9875573a-2845-47f5-aadc-70267de9246c
-- title:
--   A finite family has a uniform support-weight bound
-- statement:
--   A finite family of polynomials has a common nonnegative upper bound for the weights of all support monomials.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.exists_nonnegative_uniform_support_weight_bound
    {d t : Nat} (w : Fin d → Rat)
    (b : Fin t → MvPolynomial (Fin d) Complex) :
    ∃ C : Real, 0 ≤ C ∧ ∀ i, ∀ a ∈ (b i).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ C := by sorry
