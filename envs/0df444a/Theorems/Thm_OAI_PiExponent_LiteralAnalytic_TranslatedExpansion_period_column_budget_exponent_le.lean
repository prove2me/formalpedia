-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_period_column_budget_exponent_le
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period_column_budget_exponent_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:50:13.343195+00:00
-- url     : https://prove2.me/theorems/b4e7232e-903d-46e9-b0d1-a0d9732a37d1
-- title:
--   Weighted budget bounds the column growth exponent
-- statement:
--   Use the weighted budget and lower bounds on the weights to control the period and total-degree contributions to the growth exponent.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period_column_budget_exponent_le
    {m : ℕ} (h : ℕ) (a : Fin m → ℕ)
    (w : Fin m → ℝ) {R H w0 wstar : ℝ}
    (hR : 1 ≤ R) (hH : 0 ≤ H) (hw0 : 0 < w0) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i)
    (hcol : w0 * (h : ℝ) + ∑ i, w i * (a i : ℝ) ≤ H) :
    (h : ℝ) * R + (∑ i, (a i : ℝ)) * Real.log (2 * R) ≤
      H * (R / w0 + Real.log (2 * R) / wstar) := by sorry
