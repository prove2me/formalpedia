-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_analytic_error_budget
-- name    : OAI.PiExponent.DeterminantContradiction.analytic_error_budget
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T22:23:49.779662+00:00
-- url     : https://prove2.me/theorems/15cee980-fde0-449a-9061-c7c3eef8a709
-- title:
--   Analytic and arithmetic errors fit within the admissible budget
-- statement:
--   For admissible fixed data, the sum of the analytic and arithmetic errors is strictly below the chosen epsilon budget.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem OAI.PiExponent.DeterminantContradiction.analytic_error_budget
    {nu : ℝ} (d : FixedData nu) :
    d.analyticError + d.arithmeticError < d.epsilon := by sorry
