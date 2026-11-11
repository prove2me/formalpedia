-- Prove2me | Theorems.Thm_MinDegST_AddOne_lemma_16_5
-- name    : MinDegST.AddOne.lemma_16_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:53:56.703802+00:00
-- url     : https://prove2.me/theorems/2df95e8c-d6c7-421c-a80a-4e86c8cb8340
-- title:
--   Lemma 16.5 — every simple s–t path of the path-encoding graph determines an augmenting chain
-- statement:
--   Let $G$ be connected, $k$ a threshold for which $G$ has a spanning tree of maximum degree at most $k$, $F$ a forest of $G$ of maximum degree at most $k+1$, $\theta\in\mathbb N$, $M$ a molecular decomposition of $F$ and $\mathcal R$ its reducible regions; let $G^{enc}$ be the path-encoding graph. For every simple $s$–$t$ path $p$ of $G^{enc}$:
--   $$\exists A\ \text{read off }p,\qquad\text{and}\qquad \forall A\ \text{read off }p:\ A\ \text{is an augmenting chain w.r.t. }(F,M,\mathcal R).$$
--   "Read off" is the construction of the proof: for the region vertices $R_0^-,\dots,R_{\ell-1}^-$ of $p$ pick $w_i\in R_i$ and $z_{i+1}\notin R_i$ along the edge of $G$ that created the arc leaving $R_i^-$.
--
--   This is the dictionary between $s$–$t$ paths and augmenting chains that lets one maximum-flow computation produce many candidate chains at once.
--
--   Differences from the source:
--   - generalization: the degree bound is Δ⋆(G) (feasible = max degree ≤ Δ⋆ + 1, slack = degree ≤ Δ⋆, saturated = Δ⋆ + 1) → any threshold k for which G has a spanning tree of maximum degree ≤ k, with feasible/slack/saturated relative to k; reason: Part I's convention (p. 4); the case k = Δ⋆(G) is the source's statement (G connected has a spanning tree of maximum degree Δ⋆ ≤ n − 1)
--   - generalization: G^enc built on the θ-molecular decomposition with θ = ⌈10n/f⌉ (§16) → any θ ∈ ℕ and any molecular decomposition M with its regions; reason: the paths-to-chains argument uses no property of θ; θ = ⌈10n/f⌉ with a θ-decomposition is a special case
--   - reading: a simple s–t path 'determines' an augmenting chain → some chain can be read off the path, and every chain read off it (every choice of the edges (w_i, z_{i+1}) behind its transition arcs) is an augmenting chain; reason: the proof chooses w_i as any endpoint of the edge that created the transition arc; the statement must not be satisfiable by an unrelated chain
--   - reading: §16.1: R⁻ → z⁻ for every z ∉ V(R) adjacent to R; tree-descending X⁻ → Y⁻ for Y ∈ B ∪ R → R⁻ → z⁻ only when z⁻ exists (z in no region); Y ranges over L ∪ 𝓡 (children after contracting regions); reason: no minus vertex exists for a node inside a region, and B is not defined in Part III
-- source:
--   Bhattacharya, Farokhnejad, Saranurak, Wang, Faster Algorithms for Minimum Degree Spanning Tree, STOC 2027 submission (manuscript sha256 7d985d3b…), p. 42, Lemma 16.5

import Mathlib
import Definitions.Def_MinDegST_AddOne_Graph
import Definitions.Def_MinDegST_AddOne_Molecules
import Definitions.Def_MinDegST_AddOne_PathEncoding

namespace MinDegST.AddOne

/-- **Lemma 16.5** (threshold form, any `θ`, any molecular decomposition). Every simple `s`–`t`
path `p` of the path-encoding graph `G^enc` determines an augmenting chain: a chain can be read off
`p` (choose `w_i ∈ R_i` and `z_{i+1}` along the edge of `G` behind each transition arc of `p`), and
every chain read off `p` is an augmenting chain (Definition 14.7) w.r.t. `(G, F, k, M, 𝓡)`. -/
theorem lemma_16_5 (n : ℕ) (G : SimpleGraph (Fin n)) (k θ : ℕ) (F : SimpleGraph (Fin n))
    (M : Finset (Molecule n)) (𝓡 : Finset (Finset (Fin n)))
    (hG : G.Connected) (hk : HasSpanningTreeLE G k) (hF : IsForestOf G F) (hfeas : Feasible k F)
    (hM : IsMolDecomp F M) (h𝓡 : IsRegionsOf G F k M 𝓡)
    (p : List (EncVtx n)) (hp : IsSimpleSTPath G F k θ M 𝓡 p) :
    (∃ A : Chain n, ReadOff G F k p A) ∧
      ∀ A : Chain n, ReadOff G F k p A → IsAugmentingChain G F k M 𝓡 A := by sorry

end MinDegST.AddOne
