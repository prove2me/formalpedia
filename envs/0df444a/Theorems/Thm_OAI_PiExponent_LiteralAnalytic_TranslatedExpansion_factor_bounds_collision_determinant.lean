-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_factor_bounds_collision_determinant
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds_collision_determinant
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-17T09:45:01.43479+00:00
-- url     : https://prove2.me/theorems/f9baebc4-83c8-4aa5-bff3-3416559b9ab6
-- title:
--   Collision exponential bound for the choice determinant
-- statement:
--   For positive height, the determinant of the choice matrix satisfies the collision exponential estimate with the stated holomorphic and collision-remainder allowance.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionWeights

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds_collision_determinant
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    ‖(choiceMatrix d selection f).det‖ ≤
      Real.exp (-collisionConstant *
        (∑ a : indices d H,
          (((Finset.univ : Finset (Row d H)).filter
            (fun r => (f r).1 = a)).card : ℝ) ^ 2) +
        (actualRowCount d H : ℝ) * H *
          (d.holomorphicError + Collision.collisionRemainder (actualRowCount d H) H)) := by sorry
