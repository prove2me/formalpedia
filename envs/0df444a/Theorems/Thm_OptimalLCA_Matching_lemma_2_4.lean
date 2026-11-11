-- Prove2me | Theorems.Thm_OptimalLCA_Matching_lemma_2_4
-- name    : OptimalLCA.Matching.lemma_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:46:13.418206+00:00
-- url     : https://prove2.me/theorems/930b90e2-14f3-4330-9a75-edc0a3d3bcfc
-- title:
--   Lemma 2.4 — n₀ ≤ 2Δν_f(G) and |E| ≤ 2Δν_f(G)
-- statement:
--   If $G$ has $n_0$ nonisolated vertices and maximum degree at most $\Delta$ (an integer $\ge2$), then
--   $$n_0\le2\Delta\,\nu_f(G),\qquad |E|\le2\Delta\,\nu_f(G).$$
--   It converts additive losses proportional to $n_0$ or $|E|$ into multiplicative losses relative to $\nu_f(G)$.
--
--   Differences from the source:
--   - encoding: a graph with vertex set [n] → any finite vertex type V with a SimpleGraph (decidable adjacency); reason: relabelling; every graph on [n] is an instance
--   - reading: maximum degree at most ∆ → G.degree v ≤ Δ for every v, with 2 ≤ Δ; reason: ∆ is the degree bound of §2.1 (p. 11), 'a known integer ∆ ≥ 2'
-- source:
--   Cohen, Roghani, Optimal LCA and Sublinear Estimation for Bipartite Matching in Δ^O(1/ε) Queries, arXiv:2611.06024 (version not printed; PDF sha256 5a43ec12…3eb3), p. 13, Lemma 2.4

import Mathlib
import Definitions.Def_OptimalLCA_Matching_Graph

namespace OptimalLCA.Matching

/-- Lemma 2.4 (nonisolated vertices). If `G` has `n₀` nonisolated vertices and maximum
degree at most `Δ`, then `n₀ ≤ 2Δ ν_f(G)` and `|E| ≤ 2Δ ν_f(G)`. -/
theorem lemma_2_4 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 2 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) :
    (numNonisolated G : ℝ) ≤ 2 * (Δ : ℝ) * fracMatchingNumber G ∧
      (G.edgeFinset.card : ℝ) ≤ 2 * (Δ : ℝ) * fracMatchingNumber G := by sorry

end OptimalLCA.Matching
