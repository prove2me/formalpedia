-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurve_monomial_coeff_le_of_unit
-- name    : OAI.PiExponent.FormalInterpolation.polynomialCurve_monomial_coeff_le_of_unit
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T09:18:32.434679+00:00
-- url     : https://prove2.me/theorems/424a9c84-10d7-4d6e-b642-0d561b5e5526
-- title:
--   A constant coefficient does not increase a monomial's pole
-- statement:
--   Multiplying a monomial by a complex coefficient cannot increase its pole: for a nonzero coefficient, normalized triviality on constants preserves its order; for coefficient zero, the left side is zero by the order convention.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.polynomialCurve_monomial_coeff_le_of_unit
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (a : Fin d →₀ Nat) (c : Complex) :
    max 0 (-(polynomialCurveOrder nu
      (MvPolynomial.aeval x (MvPolynomial.monomial a c)) : Real)) ≤
    max 0 (-(polynomialCurveOrder nu
      (MvPolynomial.aeval x (MvPolynomial.monomial a (1 : Complex))) : Real)) := by sorry
