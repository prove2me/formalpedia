-- Prove2me | Theorems.Thm_OptimalLCA_Matching_lemma_2_3
-- name    : OptimalLCA.Matching.lemma_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:46:15.239399+00:00
-- url     : https://prove2.me/theorems/447cc19b-9e5f-43fe-a6b4-8a6eebedaa54
-- title:
--   Lemma 2.3 — double cover: ν(B(G)) = 2ν_f(G), projection of matchings, adjacency lists of B(G)
-- statement:
--   Let $G$ be a graph given by adjacency lists with maximum degree at most $\Delta$ (an integer $\ge2$), and $B(G)$ its bipartite double cover on $V\times\{0,1\}$.
--   (a) $\nu(B(G))=2\nu_f(G)$.
--   (b) Every matching $M$ of $B(G)$ induces the half-integral fractional matching
--   $$x_{uv}=\tfrac12\big(\mathbf 1[(u,0)(v,1)\in M]+\mathbf 1[(v,0)(u,1)\in M]\big)$$
--   of $G$, of value $|M|/2$.
--   (c) $B(G)$ has $2|V|$ vertices and maximum degree at most $\Delta$; its adjacency lists are those of $G$ with the side flipped: the $i$-th neighbour of $(u,j)$ is $(w,1-j)$ where $w$ is the $i$-th neighbour of $u$ (and the lists describe $B(G)$). Hence each degree or neighbour query to $B(G)$ is answered by one query to $G$.
--   The lemma reduces fractional matching in $G$ to matching in a bipartite graph.
--
--   Differences from the source:
--   - encoding: vertex set V × {1, 2} → V × Fin 2, sides 0 and 1; reason: index convention; (u,1)(v,2) is (u,0)(v,1)
--   - encoding: "for every graph G" with max degree ≤ Δ in (c) → G given by adjacency lists A with A.MaxDegLE Δ, 2 ≤ Δ; reason: every finite graph has adjacency lists and a degree bound Δ ≥ 2, so (a), (b) still cover every graph; Δ ≥ 2 is §2.1's standing assumption
--   - reading: each degree or neighbor query to B(G) is answered by one query to G → equality of B(G)'s adjacency lists with G's lists with the side flipped, plus A.doubleCover.toGraph = B(G); reason: the proof of (c) states exactly this list identity; it is what makes one G-query answer one B(G)-query
--   - encoding: a graph with vertex set [n] → any finite vertex type V with a SimpleGraph (decidable adjacency); reason: relabelling; every graph on [n] is an instance
-- source:
--   Cohen, Roghani, Optimal LCA and Sublinear Estimation for Bipartite Matching in Δ^O(1/ε) Queries, arXiv:2611.06024 (version not printed; PDF sha256 5a43ec12…3eb3), p. 12, Lemma 2.3

import Mathlib
import Definitions.Def_MatousekLP_Integrality_BipartiteGraph
import Definitions.Def_OptimalLCA_Matching_Graph

namespace OptimalLCA.Matching

/-- Lemma 2.3 (double cover). For every graph `G`, given by adjacency lists `A` with
maximum degree at most `Δ`: (a) `ν(B(G)) = 2 ν_f(G)`; (b) every matching `M` of `B(G)`
induces the half-integral fractional matching `x_{uv} = ½(1[(u,1)(v,2) ∈ M] +
1[(v,1)(u,2) ∈ M])` of value `|M|/2`; (c) `B(G)` has `2n` vertices, maximum degree at most
`Δ`, and its adjacency lists are those of `G` with the side flipped, so each degree or
neighbour query to `B(G)` is answered by one query to `G`. -/
theorem lemma_2_3 {V : Type*} [Fintype V] [DecidableEq V] (A : AdjLists V) (Δ : ℕ)
    (hΔ : 2 ≤ Δ) (hdeg : A.MaxDegLE Δ) :
    (matchingNumber (doubleCoverGraph A.toGraph) : ℝ) = 2 * fracMatchingNumber A.toGraph ∧
    (∀ M : Finset (Sym2 (V × Fin 2)),
      MatousekLP.Integrality.IsMatching (doubleCoverGraph A.toGraph) M →
        IsFracMatching A.toGraph (projectMatching M) ∧
        IsHalfIntegral A.toGraph (projectMatching M) ∧
        fracValue A.toGraph (projectMatching M) = (M.card : ℝ) / 2) ∧
    (Fintype.card (V × Fin 2) = 2 * Fintype.card V ∧
      A.doubleCover.toGraph = doubleCoverGraph A.toGraph ∧
      A.doubleCover.MaxDegLE Δ ∧
      ∀ (p : V × Fin 2) (i : ℕ),
        (A.doubleCover.nbrs p)[i]? = ((A.nbrs p.1)[i]?).map (fun w => (w, Fin.rev p.2))) := by sorry

end OptimalLCA.Matching
