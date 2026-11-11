-- Prove2me | Theorems.Thm_OptimalLCA_Matching_corollary_2_2
-- name    : OptimalLCA.Matching.corollary_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:46:05.571927+00:00
-- url     : https://prove2.me/theorems/8ab38776-6483-4ed4-af82-3825e0056e07
-- title:
--   Corollary 2.2 — on bipartite graphs every fractional matching has value ≤ ν(G); hence ν_f(G) = ν(G)
-- statement:
--   Let $G$ be a finite bipartite graph and $f$ a fractional matching of $G$ ($f_e\ge0$, $\sum_{e\ni v}f_e\le1$). Then
--   $$\sum_e f_e\le\nu(G),\qquad\text{hence}\qquad \nu_f(G)=\nu(G).$$
--   It is the step from fractional to integral matchings used on bipartite inputs (Theorem 1.1, both parts).
--
--   Differences from the source:
--   - encoding: a graph with vertex set [n] → any finite vertex type V with a SimpleGraph (decidable adjacency); reason: relabelling; every graph on [n] is an instance
-- source:
--   Cohen, Roghani, Optimal LCA and Sublinear Estimation for Bipartite Matching in Δ^O(1/ε) Queries, arXiv:2611.06024 (version not printed; PDF sha256 5a43ec12…3eb3), p. 12, Corollary 2.2

import Mathlib
import Definitions.Def_MatousekLP_Integrality_BipartiteGraph
import Definitions.Def_OptimalLCA_Matching_Graph

namespace OptimalLCA.Matching

/-- Corollary 2.2. On a bipartite graph every fractional matching has value at most
`ν(G)`; hence `ν_f(G) = ν(G)`. -/
theorem corollary_2_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : MatousekLP.Integrality.IsBipartite G) :
    (∀ f : Sym2 V → ℝ, IsFracMatching G f → fracValue G f ≤ (matchingNumber G : ℝ)) ∧
      fracMatchingNumber G = (matchingNumber G : ℝ) := by sorry

end OptimalLCA.Matching
