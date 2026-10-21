-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_period_columnFunction_norm_le
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period_columnFunction_norm_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T07:52:55.426285+00:00
-- url     : https://prove2.me/theorems/7cf2cbf2-b847-4a2d-b89e-c76109c7621b
-- title:
--   Weighted growth bound for period-monomial columns
-- statement:
--   Under the weighted column budget, the analytic column function is bounded on the radius-$R$ disk by an exponential whose two terms account for its period-index factor and its monomial degree.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers

open scoped BigOperators Topology
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period_columnFunction_norm_le
    {m : ℕ} (h : ℕ) (a : Fin m → ℕ) (A : Fin m →₀ ℕ)
    (w : Fin m → ℝ) {R H w0 wstar : ℝ}
    (hR : 1 ≤ R) (hH : 0 ≤ H) (hw0 : 0 < w0) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i)
    (hcol : w0 * (h : ℝ) + ∑ i, w i * (a i : ℝ) ≤ H)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖columnFunction h a A z‖ ≤
      Real.exp (H * (R / w0 + Real.log (2 * R) / wstar)) := by sorry
