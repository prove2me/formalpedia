-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedStrictSimplex_card_eventually_polynomial_bound
-- name    : OAI.PiExponent.DeterminantContradiction.weightedStrictSimplex_card_eventually_polynomial_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T02:34:21.720697+00:00
-- url     : https://prove2.me/theorems/b1fec56b-b4a6-444e-b131-5d4d9eaf3401
-- title:
--   Polynomial growth bound for strict weighted simplex cardinality
-- statement:
--   For fixed strictly positive weights, the number of natural-coordinate vectors in the strict weighted simplex is eventually bounded by a constant times $(H+1)^{m+1}$.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_Domains
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains

open Filter
open scoped Topology

theorem OAI.PiExponent.DeterminantContradiction.weightedStrictSimplex_card_eventually_polynomial_bound
    {m : ℕ} (w : Fin (m + 1) → ℝ)
    (hw : ∀ i, 0 < w i) :
    ∃ C : ℝ,
      (∀ᶠ H : ℝ in atTop,
        (Fintype.card {a // a ∈ OAI.PiExponent.strictWeightedSimplex w H} : ℝ) ≤
          C * (H + 1) ^ (m + 1)) := by sorry
