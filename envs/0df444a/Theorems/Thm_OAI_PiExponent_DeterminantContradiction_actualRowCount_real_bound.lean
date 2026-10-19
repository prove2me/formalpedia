-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualRowCount_real_bound
-- name    : OAI.PiExponent.DeterminantContradiction.actualRowCount_real_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T23:21:07.768051+00:00
-- url     : https://prove2.me/theorems/38465edb-2533-4bf9-8708-3a93f3788eb0
-- title:
--   A coordinate-box bound for the actual row count
-- statement:
--   For nonnegative H, the actual row count is bounded by the number of points in a coordinate box: K choices for the finite factor, at most H/v0+1 choices in the distinguished coordinate, and at most H+1 choices in each of the remaining m coordinates.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.DeterminantContradiction.actualRowCount_real_bound {nu : ℝ} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) (H : ℝ) (hH : 0 ≤ H) : (OAI.PiExponent.DeterminantContradiction.actualRowCount d H : ℝ) ≤ (d.K : ℝ) * (H / (d.v0 : ℝ) + 1) * (H + 1) ^ d.m := by sorry
