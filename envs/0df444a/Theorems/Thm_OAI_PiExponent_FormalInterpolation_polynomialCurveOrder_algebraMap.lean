-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurveOrder_algebraMap
-- name    : OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_algebraMap
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:16:44.872168+00:00
-- url     : https://prove2.me/theorems/bd101932-9766-434a-a405-d545f12b4d4a
-- title:
--   Constants have polynomial-curve order zero
-- statement:
--   For a nonzero complex constant $b$, every polynomial curve place evaluates $\operatorname{ord}_\nu(\overline{b})=0$. Consequently the positive and pole finsums of a nonzero constant vanish.
-- source:
--   Mission d7ce6393 FormalInterpolation AG chain; definition of PolynomialCurvePlace

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_algebraMap
    {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) {b : Complex} (hb : b ≠ 0) :
    polynomialCurveOrder nu (algebraMap Complex E b) = 0 := by sorry
