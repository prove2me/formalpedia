-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actual_minor_determinant_analytic_estimate
-- name    : OAI.PiExponent.LiteralAnalytic.actual_minor_determinant_analytic_estimate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T22:06:58.166023+00:00
-- url     : https://prove2.me/theorems/6af1a3f0-33ab-4974-9f78-5538155f9fd9
-- title:
--   Determinant analytic estimate with the original vanishing remainder
-- statement:
--   For nonnegative exponent and strictly positive height, the normalized logarithmic norm of a nonzero actual minor is bounded above by the analytic error, the original analytic remainder, and the larger of the collision and approximation penalties.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem OAI.PiExponent.LiteralAnalytic.actual_minor_determinant_analytic_estimate
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H)
    (hdet : (actualMinor d H selection).det ≠ 0) :
    Real.log ‖(actualMinor d H selection).det‖ /
        ((actualRowCount d H : ℝ) * H) ≤
      d.analyticError + analyticRemainder d H +
        max (-collisionRate d H)
          (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)) := by sorry
