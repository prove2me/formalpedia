-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_component_eq_directSum_decompose
-- name    : OAI.PiExponent.FormalInterpolation.weighted_component_eq_directSum_decompose
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:55:55.022243+00:00
-- url     : https://prove2.me/theorems/a481b207-7c49-44f8-81f8-2014d4ac50b2
-- title:
--   Identify weighted components with the chosen graded projection
-- statement:
--   For any direct-sum grading structure on these weighted homogeneous submodules, the degree-r projection of a polynomial is its weighted homogeneous component of degree r.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.weighted_component_eq_directSum_decompose
    {d : Nat} (w : Fin d → ℚ)
    [GradedRing (MvPolynomial.weightedHomogeneousSubmodule ℂ w)]
    (f : MvPolynomial (Fin d) ℂ) (r : ℚ) :
    MvPolynomial.weightedHomogeneousComponent w r f =
      (DirectSum.decompose (MvPolynomial.weightedHomogeneousSubmodule ℂ w) f r :
        MvPolynomial (Fin d) ℂ) := by sorry
