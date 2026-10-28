-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurveOrder_aeval_le_of_support_monomials_aux
-- name    : OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_aeval_le_of_support_monomials_aux
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T09:18:09.182446+00:00
-- url     : https://prove2.me/theorems/de6402e3-baf2-4094-a2ad-5119cd0de141
-- title:
--   A uniform pole bound on support terms controls polynomial evaluation
-- statement:
--   A uniform nonnegative pole bound on the coefficient-weighted monomial terms in the support bounds the pole of the evaluated polynomial, including the zero polynomial and zero evaluation.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_aeval_le_of_support_monomials_aux
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (P : MvPolynomial (Fin d) Complex) (C : Real) (hC : 0 ≤ C)
    (hterm : ∀ a ∈ P.support,
      max 0 (-(polynomialCurveOrder nu
        (MvPolynomial.aeval x (MvPolynomial.monomial a (P.coeff a))) : Real)) ≤ C) :
    max 0 (-(polynomialCurveOrder nu (MvPolynomial.aeval x P) : Real)) ≤ C := by sorry
