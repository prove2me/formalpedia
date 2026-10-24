-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurvePlace_add_pos
-- name    : OAI.PiExponent.FormalInterpolation.polynomialCurvePlace_add_pos
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:59:23.632845+00:00
-- url     : https://prove2.me/theorems/5ae6f095-0aa1-440d-909f-50db033cd359
-- title:
--   A sum of positive-value elements has positive value
-- statement:
--   For the additive valuation underlying a polynomial-curve place, the sum of two elements with strictly positive value also has strictly positive value.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.polynomialCurvePlace_add_pos
    {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) {a b : E}
    (ha : (0 : WithTop Int) < nu.1 a)
    (hb : (0 : WithTop Int) < nu.1 b) :
    (0 : WithTop Int) < nu.1 (a + b) := by sorry
