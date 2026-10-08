-- Prove2me | Theorems.Thm_IsingLTL_BeliefProp_lemma_4_1_subtree_marginal
-- name    : IsingLTL.BeliefProp.lemma_4_1_subtree_marginal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:17:46.584991+00:00
-- url     : https://prove2.me/theorems/5a3641b4-44fb-4425-bf27-f26798ddfc2a
-- title:
--   The marginal of a tree Ising measure on a subtree is an Ising measure with increased boundary fields (Lemma 4.1)
-- statement:
--   Let $T$ be a finite tree with an Ising measure $\mu^T$ (inverse temperature $\beta$, fields $\{B_i\}$, possibly some vertices pinned to $+1$, i.e. $B_i=+\infty$), and let $U$ be a subtree of $T$, $W=T\setminus U$. Let $\partial_*U$ be the vertices of $U$ joined by an edge to $W$, assume no vertex of $\partial_*U$ is pinned, and for $u\in\partial_*U$ let $\langle x_u\rangle_W$ be the root magnetization of the Ising model on the maximal subtree $\mathsf T_u$ of $W\cup\{u\}$ rooted at $u$. Then the marginal $\mu^T_U$ on $U$ is the Ising measure on $U$ with field
--   $$B'_u=\operatorname{atanh}\big(\langle x_u\rangle_W\big)\ \ (u\in\partial_*U),\qquad B'_u=B_u\ \ (u\notin\partial_*U),$$
--   and the same pins inside $U$. Moreover, if $\beta\ge0$ and all fields are nonnegative, then $B'_u\ge B_u$ for every $u\in\partial_*U$.
--
--   The lemma lets one cut a tree Ising model at a subtree, replacing the rest of the tree by effective fields; it is used repeatedly in §4 (Lemma 4.3, Lemma 4.4, Theorem 4.2).
--
--   **Formalization Note** "Subtree" means a vertex set inducing a connected subgraph. The marginal identity holds without sign conditions; the inequality $B'_u\ge B_u$ is stated under $\beta\ge0$ and $B\ge0$, the paper's standing assumptions, which its proof uses through Griffiths' inequality. Pinned vertices of $\partial_*U$ are excluded since their effective field would be $+\infty$.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 10, Lemma 4.1

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_SubtreeMarginal

namespace IsingLTL.BeliefProp

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

end IsingLTL.BeliefProp
