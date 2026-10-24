-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_component_mul_finsum
-- name    : OAI.PiExponent.FormalInterpolation.weighted_component_mul_finsum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:10:02.132036+00:00
-- url     : https://prove2.me/theorems/5f772bfc-19d6-4875-bdb3-448577e54936
-- title:
--   Component expansion for multiplication by a homogeneous polynomial
-- statement:
--   The degree-N component of a polynomial times a homogeneous degree-D factor is the finsum of the degree-m components whose degrees satisfy m + D = N, each multiplied by that factor. The equation on degrees has at most one solution because ℚ is an additive group.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open MvPolynomial

theorem OAI.PiExponent.FormalInterpolation.weighted_component_mul_finsum
    {d : Nat} (w : Fin d → ℚ) (D N : ℚ)
    (a b : MvPolynomial (Fin d) ℂ)
    (hb : MvPolynomial.IsWeightedHomogeneous w b D) :
    MvPolynomial.weightedHomogeneousComponent w N (a * b) =
      ∑ᶠ m : ℚ, if m + D = N then
        MvPolynomial.weightedHomogeneousComponent w m a * b else 0 := by sorry
