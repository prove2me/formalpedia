-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weightedStrictSimplex_mem_of_sum_lt
-- name    : OAI.PiExponent.LogarithmicJetIdeals.weightedStrictSimplex_mem_of_sum_lt
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T12:00:30.587078+00:00
-- url     : https://prove2.me/theorems/7684592f-dd8d-42ca-a864-9302c289155e
-- title:
--   Strict weighted simplex contains every exponent below its cutoff
-- statement:
--   For positive coordinate weights, every exponent function whose weighted sum is strictly below `H` belongs to the finite strict weighted simplex. Positivity bounds each coordinate by the simplex's defining finite coordinate range; the strict inequality supplies the filtered membership. The empty-dimensional case is included.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains

open scoped BigOperators
open OAI.PiExponent

theorem OAI.PiExponent.LogarithmicJetIdeals.weightedStrictSimplex_mem_of_sum_lt
    {d : ℕ} (u : Fin d → ℝ) (H : ℝ)
    (hu : ∀ i, 0 < u i) (a : Fin d → ℕ)
    (ha : (∑ i, u i * (a i : ℝ)) < H) :
    a ∈ strictWeightedSimplex u H := by sorry
