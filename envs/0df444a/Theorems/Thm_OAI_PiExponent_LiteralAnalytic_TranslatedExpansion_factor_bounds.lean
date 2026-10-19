-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_factor_bounds
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-17T09:28:41.507823+00:00
-- url     : https://prove2.me/theorems/4c3d053e-40ff-4095-af0e-e1f51c167f5e
-- title:
--   Analytic scalar and collision determinant bounds for nonzero translated choices
-- statement:
--   For positive H and nonnegative nu, a nonzero scalar product gives the selected-weight lower bound. The translated indices have nonnegative weights and the stated low-weight capacity, while the scalar product and determinant satisfy their separate exponential estimates.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionWeights

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : ChoiceFamily d H)
    (hs : (∏ r : Row d H, choiceScalar d r (f r)) ≠ 0) :
    0 < (lowIndexCount d H : ℝ) ∧
    (∀ a : indices d H, 0 ≤ translatedIndexWeight d a) ∧
    (((Finset.univ : Finset (indices d H)).filter
      (fun a => translatedIndexWeight d a ≤ (d.base.A : ℝ) * H)).card : ℝ) ≤
        (lowIndexCount d H : ℝ) ∧
    (actualRowCount d H : ℝ) * H * actualMean d H ≤
      ∑ r : Row d H, translatedIndexWeight d (f r).1 ∧
    ‖∏ r : Row d H, choiceScalar d r (f r)‖ ≤
      Real.exp (-nu * ((∑ r : Row d H, translatedIndexWeight d (f r).1) -
        (actualRowCount d H : ℝ) * H * actualMean d H) +
        (actualRowCount d H : ℝ) * H * d.translationError) ∧
    ‖(choiceMatrix d selection f).det‖ ≤
      Real.exp (-collisionConstant *
        (∑ a : indices d H,
          (((Finset.univ : Finset (Row d H)).filter
            (fun r => (f r).1 = a)).card : ℝ) ^ 2) +
        (actualRowCount d H : ℝ) * H *
          (d.holomorphicError + Collision.collisionRemainder (actualRowCount d H) H)) := by sorry
