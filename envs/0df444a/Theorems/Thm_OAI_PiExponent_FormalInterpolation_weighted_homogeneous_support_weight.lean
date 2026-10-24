-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_homogeneous_support_weight
-- name    : OAI.PiExponent.FormalInterpolation.weighted_homogeneous_support_weight
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:35:16.45164+00:00
-- url     : https://prove2.me/theorems/a9c01b82-8b17-47f3-bd99-2ee086012833
-- title:
--   Homogeneous support has the prescribed weight
-- statement:
--   Every exponent in the support of a weighted homogeneous polynomial has the polynomial's stated weight.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

theorem OAI.PiExponent.FormalInterpolation.weighted_homogeneous_support_weight
    {d : Nat} (w : Fin d → ℚ) (f : MvPolynomial (Fin d) ℂ) (t : ℚ)
    (hhom : MvPolynomial.IsWeightedHomogeneous w f t)
    (e : Fin d →₀ Nat) (he : e ∈ f.support) :
    Finsupp.weight w e = t := by sorry
