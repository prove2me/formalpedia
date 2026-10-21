-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedStrictSimplex_box_product_bound
-- name    : OAI.PiExponent.DeterminantContradiction.weightedStrictSimplex_box_product_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T02:44:25.740311+00:00
-- url     : https://prove2.me/theorems/e127d72a-536b-4029-92ef-f88550660932
-- title:
--   Polynomial bound for the coordinate box product
-- statement:
--   For fixed positive weights, the product of the coordinate range sizes is eventually bounded by a constant times (H + 1) raised to the number of coordinates.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_Domains
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains

open Filter
open scoped Topology BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedStrictSimplex_box_product_bound
    {m : ℕ} (w : Fin (m + 1) → ℝ)
    (hw : ∀ i, 0 < w i) :
    ∃ C : ℝ,
      ∀ᶠ H : ℝ in atTop,
        (∏ i : Fin (m + 1), ((⌈H / w i⌉₊ + 1 : ℕ) : ℝ)) ≤
          C * (H + 1) ^ (m + 1) := by sorry
