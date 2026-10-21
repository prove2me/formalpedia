-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_norm_summand_le
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.norm_summand_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T02:58:16.40609+00:00
-- url     : https://prove2.me/theorems/e3f06b16-67d6-4c8f-9ce5-52095cb34630
-- title:
--   Analytic and collision bound for every canonical translated summand
-- statement:
--   For nonnegative nu and positive H, every canonical translated summand satisfies the uniform exponential bound combining the analytic error, collision remainder, and the maximum of the collision and approximation rates.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.norm_summand_le
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    ‖summand d selection f‖ ≤ Real.exp (((actualRowCount d H : ℝ) * H) *
      (d.analyticError + Collision.collisionRemainder (actualRowCount d H) H +
        max (-collisionRate d H)
          (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)))) := by sorry
