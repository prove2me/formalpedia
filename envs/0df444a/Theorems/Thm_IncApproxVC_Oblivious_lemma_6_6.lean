-- Prove2me | Theorems.Thm_IncApproxVC_Oblivious_lemma_6_6
-- name    : IncApproxVC.Oblivious.lemma_6_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:43:44.960899+00:00
-- url     : https://prove2.me/theorems/5a4914e7-0384-42d5-b108-167f66039253
-- title:
--   Lemma 6.6 — a partition $(L,S,R)$ with $E(L,R)=\emptyset$, $|S|=k>0$ and $\mathrm{vol}^+(L)\le\frac{n-k}{n(1+k/\delta)}m$ has $R\ne\emptyset$
-- statement:
--   Let $G=(V,E)$ be a simple directed graph with $n$ vertices and $m$ edges, and $\delta\ge 1$ a real number with $\deg^+_G(v)\ge\delta$ for every $v\in V$. Let $(L,S,R)$ be a partition of $V$ (parts possibly empty) with $L\ne\emptyset$ and $E_G(L,R)=\emptyset$, and put $k=|S|$, $\nu=\mathrm{vol}^+_G(L)$. If $k>0$ and
--   $$\nu\ \le\ \frac{n-k}{n\,(1+k/\delta)}\cdot m,$$
--   then $R\ne\emptyset$, that is, $(L,S,R)$ is a separation triple. This volume condition is what keeps the local vertex cut problem from accepting trivial triples with empty right side.
--
--   Differences from the source:
--   - encoding: an out-degree lower bound δ ≥ 1 → δ : ℝ with 1 ≤ δ; reason: Theorem 6.8's proof applies it with δ = k/2, not always an integer
-- source:
--   Adena, Henzinger, Rutschmann, Incremental Approximate Vertex Connectivity via Almost-Linear Time Local Cut Algorithms, STOC 2027 submission (manuscript sha256 d6baac6b…), p. 21, Lemma 6.6

import Mathlib
import Definitions.Def_IncApproxVC_Oblivious_Digraph
import Definitions.Def_IncApproxVC_Oblivious_VertexConnectivity

namespace IncApproxVC.Oblivious

/-- **Lemma 6.6** (triples with non-empty right side), p. 21. Let `G` be a graph on `n` vertices
with `m` edges and `δ ≥ 1` with `deg⁺_G(v) ≥ δ` for every vertex `v`. Let `(L, S, R)` be a partition
of `V` with `L ≠ ∅` and `E_G(L, R) = ∅`, and put `k = |S|`, `ν = vol⁺_G(L)`. If `k > 0` and
`ν ≤ (n − k)/(n(1 + k/δ)) · m`, then `R ≠ ∅`, i.e. `(L, S, R)` is a separation triple. -/
theorem lemma_6_6 {V : Type*} [Fintype V] [DecidableEq V] (G : Digraph V) (hG : G.Loopless)
    (δ : ℝ) (hδ : 1 ≤ δ) (hdeg : ∀ v, δ ≤ (G.outDeg v : ℝ)) (L S R : Finset V)
    (hpart : Digraph.IsPartition3 L S R) (hL : L.Nonempty) (hLR : G.edgesBetween L R = ∅)
    (hk : 0 < S.card)
    (hν : (G.vol L : ℝ) ≤ ((Fintype.card V : ℝ) - S.card) /
      ((Fintype.card V : ℝ) * (1 + (S.card : ℝ) / δ)) * (G.numEdges : ℝ)) :
    R.Nonempty ∧ G.IsSeparationTriple L S R := by sorry

end IncApproxVC.Oblivious
