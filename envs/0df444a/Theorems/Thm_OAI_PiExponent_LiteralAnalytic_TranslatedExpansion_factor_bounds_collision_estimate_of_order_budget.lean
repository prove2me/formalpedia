-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_factor_bounds_collision_estimate_of_order_budget
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds_collision_estimate_of_order_budget
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T10:02:06.484677+00:00
-- url     : https://prove2.me/theorems/b8a128a5-6c3b-4a06-a8e8-7a8278e7a503
-- title:
--   Collision determinant estimate under a total order budget
-- statement:
--   The choice-matrix determinant satisfies the collision exponential estimate when the sum of row orders is bounded by the height budget.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds_collision_estimate_of_order_budget
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : ChoiceFamily d H)
    (horders : ((∑ r : Row d H,
      (r.2.1 0 - ((f r).2.2 : ℕ)) : ℕ) : ℝ) ≤
        (Fintype.card (Row d H) : ℝ) * H / (d.v0 : ℝ)) :
    ‖(choiceMatrix d selection f).det‖ ≤
      Real.exp (-collisionConstant *
        (∑ a : indices d H,
          (((Finset.univ : Finset (Row d H)).filter
            (fun r => (f r).1 = a)).card : ℝ) ^ 2) +
        (actualRowCount d H : ℝ) * H *
          (d.holomorphicError + Collision.collisionRemainder (actualRowCount d H) H)) := by sorry
