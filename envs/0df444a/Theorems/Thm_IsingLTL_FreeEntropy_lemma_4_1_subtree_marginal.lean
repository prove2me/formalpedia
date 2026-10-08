-- Prove2me | Theorems.Thm_IsingLTL_FreeEntropy_lemma_4_1_subtree_marginal
-- name    : IsingLTL.FreeEntropy.lemma_4_1_subtree_marginal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:14.412758+00:00
-- url     : https://prove2.me/theorems/caeec3f9-c05b-4f42-bb12-40a586a45d54
-- title:
--   Lemma 4.1 — the marginal on a subtree is an Ising measure with fields $\mathrm{atanh}\langle x_u\rangle_W\ge B_u$
-- statement:
--   Let $U$ be a subtree of a finite tree $T$, $W=T\setminus U$, and $\partial_*U$ the vertices of $U$ joined by an edge to $W$. For $u\in\partial_*U$ let $\langle x_u\rangle_W$ be the root magnetization of the Ising model on the maximal subtree $T_u$ of $W\cup\{u\}$ rooted at $u$. Then the marginal $\mu^T_U$ on $U$ of the Ising measure on $T$ is the Ising measure on $U$ with magnetic field
--   $$B'_u=\operatorname{atanh}(\langle x_u\rangle_W)\ \text{ for } u\in\partial_*U,\qquad B'_u=B_u\ \text{ for } u\notin\partial_*U,$$
--   and, when $\beta\ge0$ and all fields are nonnegative, $B'_u\ge B_u$ for $u\in\partial_*U$.
--
--   **Formalization Note** Vertices with field $+\infty$ (pins) are allowed anywhere except on $\partial_*U$; pins in $U$ remain pins of the marginal. The identity of marginals holds without sign conditions; the inequality $B'_u\ge B_u$ is stated under $\beta\ge0$ and $B\ge0$, the standing assumptions used by the paper's argument.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 10, Lemma 4.1

import Mathlib
import Definitions.Def_IsingLTL_FreeEntropy_SubtreeMarginal

namespace IsingLTL.FreeEntropy

/-- **Lemma 4.1** (Dembo–Montanari, arXiv:0804.4726v3, p. 10). For a subtree `U` of a finite tree
`T`, let `∂_*U` be the vertices of `U` joined by an edge to `W = T \ U`, and for `u ∈ ∂_*U` let
`⟨x_u⟩_W` be the root magnetization of the Ising model on the maximal subtree `T_u` of `W ∪ {u}`
rooted at `u`. Then the marginal `μ^T_U` on `U` of the Ising measure on `T` is an Ising measure on
`U` with field `B′_u = atanh(⟨x_u⟩_W) ≥ B_u` for `u ∈ ∂_*U` and `B′_u = B_u` for `u ∉ ∂_*U`.

Formalization Note: the tree is `G` on the finite type `V` (`G.IsTree`), `U` a vertex set inducing
a connected subgraph. Fields `B_i = +∞` (the convention of p. 10) are allowed as pins `S`, at any
vertex not in `∂_*U` (a pinned `u ∈ ∂_*U` would have `B′_u = +∞`); pins in `U` stay pins of the
marginal. The marginal identity is stated without sign conditions; the inequality `B′_u ≥ B_u`
is stated under `β ≥ 0` and `B ≥ 0`, the standing assumptions of the paper that its proof (via
Griffiths' inequality) uses. -/
theorem lemma_4_1_subtree_marginal {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (β : ℝ) (B : V → ℝ)
    (S U : Finset V) (hU : (G.induce (↑U : Set V)).Connected)
    (hS : ∀ u ∈ outerBoundary G U, u ∉ S) :
    marginalOn Finset.univ U (isingOn G β B S Finset.univ) =
        isingOn G β
          (fun v => if v ∈ outerBoundary G U then cavityField G β B S U v else B v) S U ∧
      (0 ≤ β → (∀ v, 0 ≤ B v) →
        ∀ u ∈ outerBoundary G U, B u ≤ cavityField G β B S U u) := by sorry

end IsingLTL.FreeEntropy
