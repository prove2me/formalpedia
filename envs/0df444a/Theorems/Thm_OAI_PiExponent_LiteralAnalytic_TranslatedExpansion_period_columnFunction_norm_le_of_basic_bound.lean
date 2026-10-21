-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_period_columnFunction_norm_le_of_basic_bound
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period_columnFunction_norm_le_of_basic_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:49:32.547976+00:00
-- url     : https://prove2.me/theorems/11b5ad5f-826d-4ed9-bb3f-bb981d4858d6
-- title:
--   Basic norm bound for period-monomial columns
-- statement:
--   Bound the norm of a period-monomial column on a disk of radius at least one, without using a weighted column budget.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers

open scoped BigOperators Topology

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period_columnFunction_norm_le_of_basic_bound
    {m : ℕ} (h : ℕ) (a : Fin m → ℕ) (A : Fin m →₀ ℕ)
    {R : ℝ} (hR : 1 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic.columnFunction h a A z‖ ≤
      Real.exp ((h : ℝ) * R + (∑ i, (a i : ℝ)) * Real.log (2 * R)) := by sorry
