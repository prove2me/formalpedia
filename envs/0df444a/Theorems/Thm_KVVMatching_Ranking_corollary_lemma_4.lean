-- Prove2me | Theorems.Thm_KVVMatching_Ranking_corollary_lemma_4
-- name    : KVVMatching.Ranking.corollary_lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:52:24.306736+00:00
-- url     : https://prove2.me/theorems/e82fe103-6be6-4d1b-8c65-eb4172b5be0a
-- title:
--   Corollary to Lemma 4 — expected size from double coverage
-- statement:
--   On an $n\times n$ upper-triangular adjacency matrix with unit diagonal, let $M$ be the matching produced by RANKING in the rows-arrive picture, with uniformly random row order. Let $D(M)$ be the indices whose row and column are both matched. Then
--
--   $$\mathbb E|M|=\frac n2+\frac12\mathbb E|D(M)|.$$
--
--   The assertion applies to RANKING's output itself; its coverage property follows from the algorithm and the diagonal condition. The expectation is over all $n!$ row orders.
-- source:
--   Karp, Vazirani, Vazirani, An Optimal Algorithm for On-line Bipartite Matching, STOC 1990, p. 354, Corollary following Lemma 4

import Definitions.Def_KVVMatching_Ranking_Algorithms

namespace KVVMatching.Ranking

/-- Corollary to Lemma 4, p. 354: expected matching cardinality in terms of
indices whose row and column are both covered. -/
theorem corollary_lemma_4 {n : ℕ} (adj : Fin n → Fin n → Prop)
    (hdiag : ∀ i, adj i i)
    (hupper : ∀ i j, adj i j → i ≤ j) :
    rowRankingExpectation adj = (n : ℝ) / 2 +
      (1 / 2 : ℝ) * ((n.factorial : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin n),
          ((doubleCovered (rowRankingMatching adj σ)).card : ℝ)) := by sorry

end KVVMatching.Ranking
