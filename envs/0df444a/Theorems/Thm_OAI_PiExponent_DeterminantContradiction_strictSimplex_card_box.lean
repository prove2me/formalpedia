-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_strictSimplex_card_box
-- name    : OAI.PiExponent.DeterminantContradiction.strictSimplex_card_box
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T23:26:15.282436+00:00
-- url     : https://prove2.me/theorems/1f78e56a-1ee7-40c8-b3c2-8f09cca56db4
-- title:
--   Coordinate box bound for the strict weighted simplex
-- statement:
--   For nonnegative H, the number of points in the strict weighted simplex used by the row domain is at most the product of the distinguished-coordinate bound H/v0+1 and H+1 for each remaining coordinate.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.DeterminantContradiction.strictSimplex_card_box {nu : ℝ} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) (H : ℝ) (hH : 0 ≤ H) : (Fintype.card (↑(OAI.PiExponent.strictWeightedSimplex (OAI.PiExponent.InterpolationMatrix.rowWeights d.v0 d.base.theta (OAI.PiExponent.MatrixArithmetic.logWeights (OAI.PiExponent.DeterminantContradiction.finiteDenominators d))) H) : Type) : ℝ) ≤ (H / (d.v0 : ℝ) + 1) * (H + 1) ^ d.m := by sorry
