-- Prove2me | Theorems.Thm_KVVMatching_Ranking_ranking_guarantee
-- name    : KVVMatching.Ranking.ranking_guarantee
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:52:35.499332+00:00
-- url     : https://prove2.me/theorems/e373f321-9afd-4335-8472-5b2f6f72eeb4
-- title:
--   Theorem 1 with Lemmas 3 and 5 — RANKING's n(1 − 1/e) − o(n) guarantee
-- statement:
--   For every $\varepsilon>0$, there is a threshold $N$ such that for every $n\ge N$ and every bipartite graph on $n$ boys and $n$ girls that contains a perfect matching, RANKING's expected matching size satisfies
--
--   $$\mathbb E_{\pi\sim\mathrm{Unif}(S_n)}|M_{\mathrm{RANKING}}(G,\pi)|\ge (1-e^{-1}-\varepsilon)n.$$
--
--   Girls arrive in the fixed order $n,n-1,\ldots,1$; each girl takes her highest-priority adjacent unmatched boy. The expectation is the uniform average over all $n!$ rankings of boys. Because the graph is arbitrary, this also covers any preselected girl-arrival order by relabeling.
--
--   The paper writes the lower-order error as $o(n)$. Formally, the same $N$ works for every perfect-matchable graph of size $n$, expressing the worst-case performance measure $p(\mathrm{RANKING})$ rather than a separate asymptotic statement for each graph. The claim is the RANKING guarantee obtained from the paper's Theorem 1 together with Lemmas 3 and 5.
-- source:
--   Karp, Vazirani, Vazirani, An Optimal Algorithm for On-line Bipartite Matching, STOC 1990, p. 356, Theorem 1 (with Lemmas 3 and 5, p. 354); DOI 10.1145/100216.100262

import Definitions.Def_KVVMatching_Ranking_Algorithms
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPerfectMatchingBij

namespace KVVMatching.Ranking

/-- The RANKING guarantee drawn from Theorem 1 with Lemmas 3 and 5.
The asymptotic threshold is uniform over all graphs of a given size. -/
theorem ranking_guarantee (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (n : ℕ), N ≤ n → ∀ (adj : Fin n → Fin n → Prop),
      (∃ τ : Fin n ≃ Fin n,
        DiscreteConvex.IntegralConvexityB.IsPerfectMatchingBij
          {p : Fin n × Fin n | adj p.1 p.2} τ) →
      (1 - Real.exp (-1) - ε) * (n : ℝ) ≤ rankingExpectation adj := by sorry

end KVVMatching.Ranking
