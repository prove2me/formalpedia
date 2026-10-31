-- Prove2me | Theorems.Thm_KnapsackFacets_lemma_1
-- name    : KnapsackFacets.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:13:26.944001+00:00
-- url     : https://prove2.me/theorems/3cf9810f-cc17-468f-b8c6-07185bd5e86c
-- title:
--   Lemma 1 ([6]) — $f_j=\sum_{i=1}^{j-2}f_i$ for $j\ge3$
-- statement:
--   **Lemma 1.** For the shifted Fibonacci sequence $f$ of (1)–(2) and every $j\ge3$,
--   $$
--   f_j=\sum_{i=1}^{j-2}f_i .
--   $$
--
--   It is used in Claims A and B of the proof of Theorem 4.
--
--   Differences from the source: none.
-- source:
--   Chen & Zhu, The Complexity of Recognizing Facets for the Knapsack Polytope, arXiv:2211.03311v3, Lemma 1, p.6

import Definitions.Def_KnapsackFacets_ShiftedFib

set_option autoImplicit false

namespace KnapsackFacets

/-- **Lemma 1 ([6]).** "For j ≥ 3, f_j = Σ_{i=1}^{j−2} fᵢ." Chen & Zhu, arXiv:2211.03311v3,
Lemma 1, p.6.

**Formalization Note.** `f` is `shiftedFib` (1-indexed, `f₁ = f₂ = f₃ = 1`); `j − 2` is exact
since `j ≥ 3`. -/
theorem lemma_1 (j : ℕ) (hj : 3 ≤ j) :
    shiftedFib j = ∑ i ∈ Finset.Icc 1 (j - 2), shiftedFib i := by sorry

end KnapsackFacets
