-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weightedHomogeneousComponent_mul_of_right_homogeneous
-- name    : OAI.PiExponent.FormalInterpolation.weightedHomogeneousComponent_mul_of_right_homogeneous
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:26:00.990659+00:00
-- url     : https://prove2.me/theorems/31c7dfe7-2079-4fc5-90f4-53bc95e46be7
-- title:
--   Projection of a product with a homogeneous factor
-- statement:
--   For rationally weighted polynomials, the degree-E component of a product with a homogeneous degree-D factor is the product of that factor and the degree-(E-D) component of the other factor. This holds without positivity assumptions on either degree.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.weightedHomogeneousComponent_mul_of_right_homogeneous
    {d : Nat} (w : Fin d → ℚ) (E D : ℚ)
    (a p : MvPolynomial (Fin d) Complex)
    (hp : MvPolynomial.IsWeightedHomogeneous w p D) :
    MvPolynomial.weightedHomogeneousComponent w E (a * p) =
      MvPolynomial.weightedHomogeneousComponent w (E - D) a * p := by sorry
