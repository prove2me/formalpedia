-- Prove2me | Theorems.Thm_OptimalLCA_Matching_lemma_5_8
-- name    : OptimalLCA.Matching.lemma_5_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:47:51.157185+00:00
-- url     : https://prove2.me/theorems/64970a93-7569-4377-98f2-e8b677910c65
-- title:
--   Lemma 5.8 — initial potential Φ₀(y, q*) ≤ B_Δ ν_f(G)
-- statement:
--   Let $G$ have maximum degree at most $\Delta\ge2$, let $M^*$ be a maximum matching of $B(G)$ and $q^*$ the comparison distributions of Lemma 3.1(c) built from it ($u$ puts unit mass on $v$ if $(u,1)(v,2)\in M^*$, else on its dummy). If $y\in\{-1,1\}^V$ has at most $2\nu_f(G)$ positive coordinates among the nonisolated vertices, then
--   $$\Phi_0(y,q^*)\le B_\Delta\,\nu_f(G),\qquad B_\Delta=200+400\log(2\Delta),$$
--   where $\Phi_0(w)=D^{32}_{z_0}(w)+64K_{\bar q_0}(w_q)$ with sums over nonisolated vertices.
--
--   Differences from the source:
--   - reading: the comparison distributions constructed in Lemma 3.1(c) → q* built from any maximum matching M* of B(G); reason: the construction in the proof of Lemma 3.1(c) fixes an arbitrary maximum matching
--   - encoding: sides {1, 2} of B(G) → Fin 2 sides 0, 1; reason: index convention
--   - encoding: a graph with vertex set [n] → any finite vertex type V with a SimpleGraph (decidable adjacency); reason: relabelling; every graph on [n] is an instance
-- source:
--   Cohen, Roghani, Optimal LCA and Sublinear Estimation for Bipartite Matching in Δ^O(1/ε) Queries, arXiv:2611.06024 (version not printed; PDF sha256 5a43ec12…3eb3), p. 26, Lemma 5.8

import Mathlib
import Definitions.Def_MatousekLP_Integrality_BipartiteGraph
import Definitions.Def_OptimalLCA_Matching_Graph
import Definitions.Def_OptimalLCA_Matching_SaddlePoint
import Definitions.Def_OptimalLCA_Matching_Optimizer

namespace OptimalLCA.Matching

/-- Lemma 5.8 (initial potential). Let `q*` be the comparison distributions of
Lemma 3.1(c), built from a maximum matching `M*` of `B(G)`. If `y ∈ {-1, 1}^V` has at most
`2 ν_f(G)` positive coordinates among the nonisolated vertices, then
`Φ₀(y, q*) ≤ B_Δ ν_f(G)`. -/
theorem lemma_5_8 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 2 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (M : Finset (Sym2 (V × Fin 2)))
    (hM : MatousekLP.Integrality.IsMatching (doubleCoverGraph G) M)
    (hMmax : M.card = matchingNumber (doubleCoverGraph G))
    (y : V → ℝ) (hy : ∀ v, y v = -1 ∨ y v = 1)
    (hpos : (((nonisolated G).filter (fun v => 0 < y v)).card : ℝ) ≤
      2 * fracMatchingNumber G) :
    potential0 G Δ (y, qStar G M) ≤ bDelta Δ * fracMatchingNumber G := by sorry

end OptimalLCA.Matching
