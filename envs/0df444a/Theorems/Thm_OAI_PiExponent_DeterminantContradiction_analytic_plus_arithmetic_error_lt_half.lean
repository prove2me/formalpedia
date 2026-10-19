-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_analytic_plus_arithmetic_error_lt_half
-- name    : OAI.PiExponent.DeterminantContradiction.analytic_plus_arithmetic_error_lt_half
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T22:23:37.814847+00:00
-- url     : https://prove2.me/theorems/1868b959-40f9-4c60-82fa-beb0d7917bfe
-- title:
--   Analytic and arithmetic errors fit within the parameter budget
-- statement:
--   For every admissible fixed data set, the analytic and arithmetic errors together are strictly below one half.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem OAI.PiExponent.DeterminantContradiction.analytic_plus_arithmetic_error_lt_half
    {nu : ℝ} (d : FixedData nu) :
    d.analyticError + d.arithmeticError < 1 / 2 := by sorry
