-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurve_monomial_pole_le
-- name    : OAI.PiExponent.FormalInterpolation.polynomialCurve_monomial_pole_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T09:11:37.163104+00:00
-- url     : https://prove2.me/theorems/ac317182-9ff8-49b1-bcf8-27aa6f69066f
-- title:
--   Weighted degree bounds the pole of an evaluated monomial
-- statement:
--   For strictly positive coordinate weights, a monomial whose weighted degree is at most N evaluates to an element with pole at most N times the weighted coordinate pole supremum. The empty exponent vector and vanishing coordinates are included.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.polynomialCurve_monomial_pole_le
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E) (w : Fin d → Rat)
    (hw : ∀ i, 0 < (w i : Real)) (N : Nat)
    (a : Fin d →₀ Nat)
    (hdeg : (∑ i : Fin d, (a i : Real) * (w i : Real)) ≤ (N : Real)) :
    max 0 (-(polynomialCurveOrder nu
      (MvPolynomial.aeval x (MvPolynomial.monomial a (1 : Complex))) : Real)) ≤
      (N : Real) * polynomialCurvePole nu x w := by sorry
