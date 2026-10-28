-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurveOrder_aeval_le_of_support_monomials
-- name    : OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_aeval_le_of_support_monomials
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T09:11:19.195438+00:00
-- url     : https://prove2.me/theorems/703afee6-031d-42c1-9c9c-3e8adafba5ba
-- title:
--   A uniform monomial pole bound controls polynomial evaluation
-- statement:
--   If every evaluated support monomial of a polynomial has pole at most a nonnegative real C, then the evaluated polynomial has pole at most C. This is the valuation inequality for finite sums, with the zero polynomial and zero evaluation covered by the `max 0` convention.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_aeval_le_of_support_monomials
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (P : MvPolynomial (Fin d) Complex) (C : Real) (hC : 0 ≤ C)
    (hterm : ∀ a ∈ P.support,
      max 0 (-(polynomialCurveOrder nu
        (MvPolynomial.aeval x (MvPolynomial.monomial a (P.coeff a))) : Real)) ≤ C) :
    max 0 (-(polynomialCurveOrder nu (MvPolynomial.aeval x P) : Real)) ≤ C := by sorry
