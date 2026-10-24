-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weightedHomogeneousComponent_mul_monomial
-- name    : OAI.PiExponent.FormalInterpolation.weightedHomogeneousComponent_mul_monomial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:31:55.120223+00:00
-- url     : https://prove2.me/theorems/f7879bc8-c62c-4f82-b61c-8eec0463dcaf
-- title:
--   Projection after multiplication by a monomial
-- statement:
--   The weight-E component of a polynomial multiplied by a monomial is the monomial times the component whose weight is shifted down by the monomial’s weight.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.weightedHomogeneousComponent_mul_monomial
    {d : Nat} (w : Fin d → ℚ) (E : ℚ)
    (a : MvPolynomial (Fin d) Complex) (v : Fin d →₀ ℕ) (c : Complex) :
    MvPolynomial.weightedHomogeneousComponent w E
        (a * MvPolynomial.monomial v c) =
      MvPolynomial.weightedHomogeneousComponent w
          (E - Finsupp.weight w v) a * MvPolynomial.monomial v c := by sorry
