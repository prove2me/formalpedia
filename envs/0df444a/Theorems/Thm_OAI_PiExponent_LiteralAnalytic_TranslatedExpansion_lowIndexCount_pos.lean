-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_lowIndexCount_pos
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.lowIndexCount_pos
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T10:02:47.458328+00:00
-- url     : https://prove2.me/theorems/b9ad3023-64a7-46b6-a40a-d892be322bec
-- title:
--   Positivity of the low-index count
-- statement:
--   When $H>0$, the zero exponent vector is in the weighted simplex counted by `lowIndexCount`, so that finite set has positive cardinality.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionWeights

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.lowIndexCount_pos {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) : 0 < (lowIndexCount d H : ℝ) := by sorry
