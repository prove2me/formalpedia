-- Prove2me | Theorems.Thm_KVVMatching_Ranking_lemma_3
-- name    : KVVMatching.Ranking.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:51:59.691952+00:00
-- url     : https://prove2.me/theorems/623f8dc1-7a74-467b-bba8-852b80d8b651
-- title:
--   Lemma 3 — upper-triangular worst-case reduction
-- statement:
--   Let $B$ be an $n\times n$ bipartite adjacency matrix with a perfect matching. In the dual view, rows arrive in uniformly random order and column $n$ has highest priority. There exists another adjacency matrix $B'$ with every diagonal entry equal to one and with no entry below the diagonal, whose expected RANKING matching is no larger than that of $B$.
--
--   $$B'_{ii}=1,\qquad B'_{ij}=1\Rightarrow i\le j,\qquad \mathbb E|M_{\mathrm{RANKING}}(B')|\le\mathbb E|M_{\mathrm{RANKING}}(B)|.$$
--
--   Thus the worst-case expected performance can be studied among matrices that are upper triangular and still possess a perfect matching.
--
--   **Formalization Note** The perfect matching uses a previously published predicate saying that a bijection selects an edge at every row. Both expectations are finite uniform averages over row permutations.
-- source:
--   Karp, Vazirani, Vazirani, An Optimal Algorithm for On-line Bipartite Matching, STOC 1990, p. 354, Lemma 3 and proof (diagonal renumbering)

import Definitions.Def_KVVMatching_Ranking_Algorithms
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPerfectMatchingBij

namespace KVVMatching.Ranking

/-- Lemma 3, p. 354: a unit-diagonal upper triangular matrix is no better
for RANKING than any given graph with a perfect matching. -/
theorem lemma_3 {n : ℕ} (adj : Fin n → Fin n → Prop)
    (hperfect : ∃ τ : Fin n ≃ Fin n,
      DiscreteConvex.IntegralConvexityB.IsPerfectMatchingBij
        {p : Fin n × Fin n | adj p.1 p.2} τ) :
    ∃ adj' : Fin n → Fin n → Prop,
      (∀ i, adj' i i) ∧
      (∀ i j, adj' i j → i ≤ j) ∧
      rowRankingExpectation adj' ≤ rowRankingExpectation adj := by sorry

end KVVMatching.Ranking
