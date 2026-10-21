-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_period_columnFunction_norm_le_of_factorized_bound
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period_columnFunction_norm_le_of_factorized_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:58:58.526198+00:00
-- url     : https://prove2.me/theorems/fd54aa74-c9f3-441b-a4c1-f0d9db81a6e1
-- title:
--   Factorized norm bound for period-monomial columns
-- statement:
--   Bound the norm of a period-monomial column by separating the exponential-in-height factor from the coefficient and radius contribution.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers

open scoped BigOperators Topology

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period_columnFunction_norm_le_of_factorized_bound
    {m : ℕ} (h : ℕ) (a : Fin m → ℕ) (A : Fin m →₀ ℕ)
    {R : ℝ} (hR : 1 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic.columnFunction h a A z‖ ≤
      Real.exp ((h : ℝ) * R) * Real.exp ((∑ i, (a i : ℝ)) * Real.log (2 * R)) := by sorry
