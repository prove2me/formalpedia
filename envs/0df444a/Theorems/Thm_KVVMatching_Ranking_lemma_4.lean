-- Prove2me | Theorems.Thm_KVVMatching_Ranking_lemma_4
-- name    : KVVMatching.Ranking.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:52:10.730804+00:00
-- url     : https://prove2.me/theorems/b88d7b73-cdfe-4eea-8ea2-a1a3ef998c9f
-- title:
--   Lemma 4 — matching size from doubly covered indices
-- statement:
--   Let $B$ be an $n\times n$ upper-triangular adjacency matrix with unit diagonal, and let $M$ be a matching using its edges. Suppose that for each index $i$, row $i$ or column $i$ is matched, possibly both. Write $D$ for the indices where both are matched. Then
--
--   $$|M|=\frac{n+|D|}{2}.$$
--
--   This counting identity turns the analysis of matching size into an analysis of the indices covered on both sides. The disjunction in the hypothesis is inclusive.
-- source:
--   Karp, Vazirani, Vazirani, An Optimal Algorithm for On-line Bipartite Matching, STOC 1990, p. 354, Lemma 4

import Definitions.Def_KVVMatching_Ranking_Algorithms

namespace KVVMatching.Ranking

/-- Lemma 4, p. 354: counting the vertices covered by a matching. -/
theorem lemma_4 {n : ℕ} (adj : Fin n → Fin n → Prop)
    (hdiag : ∀ i, adj i i)
    (hupper : ∀ i j, adj i j → i ≤ j)
    (M : Finset (Fin n × Fin n))
    (hM : IsMatching M)
    (hEdges : ∀ e ∈ M, adj e.1 e.2)
    (hCover : ∀ i : Fin n, firstMatched M i ∨ secondMatched M i) :
    (M.card : ℝ) = ((n : ℝ) + (doubleCovered M).card) / 2 := by sorry

end KVVMatching.Ranking
