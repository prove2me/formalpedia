-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedStrictSimplex_box_product_bound_explicit
-- name    : OAI.PiExponent.DeterminantContradiction.weightedStrictSimplex_box_product_bound_explicit
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-17T02:48:13.25067+00:00
-- url     : https://prove2.me/theorems/1c268fd3-bb2d-41c6-8de7-deb7df1c8020
-- title:
--   Explicit polynomial bound for the coordinate box product
-- statement:
--   For fixed positive weights, the coordinate box product is eventually bounded by the explicit constant product of (2 + 1 / w i) times (H + 1) to the number of coordinates.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_Domains
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains

open Filter
open scoped Topology BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedStrictSimplex_box_product_bound_explicit
    {m : ℕ} (w : Fin (m + 1) → ℝ)
    (hw : ∀ i, 0 < w i) :
    ∀ᶠ H : ℝ in atTop,
      (∏ i : Fin (m + 1), ((⌈H / w i⌉₊ + 1 : ℕ) : ℝ)) ≤
        (∏ i : Fin (m + 1), (1 / w i + 2)) * (H + 1) ^ (m + 1) := by sorry
