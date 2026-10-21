-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedStrictSimplex_box_card_bound
-- name    : OAI.PiExponent.DeterminantContradiction.weightedStrictSimplex_box_card_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T02:43:57.299229+00:00
-- url     : https://prove2.me/theorems/ea135f66-015d-4ef3-a904-49f34b76e098
-- title:
--   Coordinate box bound for strict weighted simplex cardinality
-- statement:
--   For any real H and strictly positive weights, the cardinality of the strict weighted simplex is at most the product of the sizes of its coordinate ranges. If H is nonpositive, the strict simplex is empty; for positive H, each coordinate is bounded by the corresponding truncated ceiling.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_Domains
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedStrictSimplex_box_card_bound
    {m : ℕ} (w : Fin (m + 1) → ℝ)
    (hw : ∀ i, 0 < w i) (H : ℝ) :
    (Fintype.card {a // a ∈ OAI.PiExponent.strictWeightedSimplex w H} : ℝ) ≤
      ∏ i : Fin (m + 1), ((⌈H / w i⌉₊ + 1 : ℕ) : ℝ) := by sorry
