-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_support_monomials_in_ideal
-- name    : OAI.PiExponent.FormalInterpolation.support_monomials_in_ideal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:35:34.503183+00:00
-- url     : https://prove2.me/theorems/0fd2d3b3-c97c-428a-82e8-955bca3113f8
-- title:
--   Membership from supported monomials
-- statement:
--   If each monomial term indexed by the finite support of a multivariate polynomial belongs to an ideal, then the polynomial belongs to that ideal.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

theorem OAI.PiExponent.FormalInterpolation.support_monomials_in_ideal
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) ℂ))
    (f : MvPolynomial (Fin d) ℂ)
    (hterms : ∀ e ∈ f.support,
      MvPolynomial.monomial e (f.coeff e) ∈ I) :
    f ∈ I := by sorry
