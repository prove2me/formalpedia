-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurveOrder_pow
-- name    : OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_pow
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T18:06:43.092968+00:00
-- url     : https://prove2.me/theorems/a70d4322-a477-4ba6-8fc7-0b53d9358da8
-- title:
--   The curve order of a power scales by its exponent
-- statement:
--   The order induced by a multiplicative valuation scales by a natural exponent, including exponent zero and the zero-element case under the order’s `untop₀` convention.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Mathlib.FieldTheory.IsAlgClosed.Basic

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_pow
    {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (f : E) (n : Nat) :
    (polynomialCurveOrder nu (f ^ n) : Real) =
      (n : Real) * (polynomialCurveOrder nu f : Real) := by sorry
