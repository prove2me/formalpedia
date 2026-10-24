-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_component_mem
-- name    : OAI.PiExponent.FormalInterpolation.weighted_component_mem
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T10:01:06.845044+00:00
-- url     : https://prove2.me/theorems/a2528cb8-c846-4ad8-aa3c-1b26da2cee5e
-- title:
--   Weighted components preserve membership in a homogeneous ideal
-- statement:
--   For an ideal homogeneous under the weighted grading, each weighted homogeneous component of an element of the ideal remains in the ideal.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.weighted_component_mem
    {d : Nat} (w : Fin d → ℚ)
    [GradedRing (MvPolynomial.weightedHomogeneousSubmodule ℂ w)]
    (I : Ideal (MvPolynomial (Fin d) ℂ))
    (hI : I.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule ℂ w))
    {f : MvPolynomial (Fin d) ℂ} (hf : f ∈ I) (r : ℚ) :
    MvPolynomial.weightedHomogeneousComponent w r f ∈ I := by
  sorry
