-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_component_mul_for_relation_extract
-- name    : OAI.PiExponent.FormalInterpolation.weighted_component_mul_for_relation_extract
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:06:51.262153+00:00
-- url     : https://prove2.me/theorems/7bb4ec35-c24c-482a-8cde-fa31d8c1a12f
-- title:
--   Weighted component of a product with a homogeneous factor
-- statement:
--   When one factor is weighted homogeneous of degree D, the degree-N component of the product is the product of that factor and the degree-(N-D) component of the other factor. The identity also holds for zero factors and empty components.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

theorem OAI.PiExponent.FormalInterpolation.weighted_component_mul_for_relation_extract
    {d : Nat} (w : Fin d → ℚ) (D N : ℚ)
    (a b : MvPolynomial (Fin d) ℂ)
    (hb : MvPolynomial.IsWeightedHomogeneous w b D) :
    MvPolynomial.weightedHomogeneousComponent w N (a * b) =
      MvPolynomial.weightedHomogeneousComponent w (N - D) a * b := by sorry
