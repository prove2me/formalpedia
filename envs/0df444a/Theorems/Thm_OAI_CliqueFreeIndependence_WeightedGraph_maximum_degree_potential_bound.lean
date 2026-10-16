-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_maximum_degree_potential_bound
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.maximum_degree_potential_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:11:06.549995+00:00
-- url     : https://prove2.me/theorems/c6b13e23-88bd-4f9c-8b6f-eeca91868686
-- title:
--   The variational potential of a $K_{k+2}$-free graph of maximum degree $\Delta$ is bounded via an independent set
-- statement:
--   Let $G$ be a finite simple graph on a finite vertex set $V$. For a weight $q\colon V\to\mathbb{R}$ let $E_G(q)=\sum_{\{u,v\}\in E(G)}q_uq_v$ be its edge mass and $T_G(q)=\sum q_uq_vq_z$ its triangle mass, where the sum runs over the unordered triangles $\{u,v,z\}$ of $G$. Define the potential
--   $$
--   \Phi_G(q)=\sum_{v\in V}q_v\,(1-\log q_v)-E_G(q),
--   $$
--   with the convention $0\log0=0$. A weight $w$ is a maximiser for $G$ if $w_v\ge0$ for all $v$ and $\Phi_G(q)\le\Phi_G(w)$ for every $q$ with $q_v\ge0$ for all $v$. A graph is $K_{k+2}$-free if it contains no clique on $k+2$ vertices, and a set $I\subseteq V$ is independent if no two of its vertices are adjacent.
--
--   Let $k\in\mathbb{N}$ and let $B\ge0$ and $\Delta\ge3$ be real numbers. Assume the triangle hypothesis: for every finite simple graph $H$ and every maximiser $w$ for $H$, if $H$ is $K_{k+2}$-free then $T_H(w)\le B\,E_H(w)$. Then for every $K_{k+2}$-free graph $G$ on $V$ in which every vertex has degree at most $\Delta$ there is an independent set $I\subseteq V$ such that
--   $$
--   \Phi_G(q)\le\Big(3+\frac{3B}{2}\Big)\log\Delta\cdot|I|\qquad\text{for every }q\colon V\to[0,\infty).
--   $$
--
--   Since $|I|$ is at most the independence number $\alpha(G)$, the maximum of $\Phi_G$ over nonnegative weights is at most $(3+3B/2)\,\alpha(G)\log\Delta$. The bound controls the potential itself rather than a surrogate objective. Evaluating $\Phi_G$ at a constant weight then gives a lower bound of order $|V|\log\Delta/\Delta$ on the independence number of $K_{k+2}$-free graphs of maximum degree $\Delta$.
--
--   **Formalization Note** The triangle hypothesis quantifies over all finite vertex types in the same universe as $V$, and maximisers are `IsOptimizer`. The vertex term $t(1-\log t)$ is `vertexPotential t`, and the convention that `Real.log` vanishes at $0$ makes it vanish at $t=0$. Degrees are natural numbers compared with $\Delta$ as real numbers, and $I$ is a `Finset V` with `G.IsIndepSet I`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/IndependentSet.lean#L118-L167

import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
import Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState
import Definitions.Def_OAI_Combinatorics_CliqueFree_Projection
import Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Reach
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteKernel
import Definitions.Def_OAI_Combinatorics_CliqueFree_LocalWalk
import Definitions.Def_OAI_Combinatorics_CliqueFree_WalkEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteCoupling
import Definitions.Def_OAI_Combinatorics_CliqueFree_VertexSplitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Peeling

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
variable {V : Type u} [Fintype V]

theorem OAI.CliqueFreeIndependence.WeightedGraph.maximum_degree_potential_bound (k : ℕ) {B Δ : ℝ} (hB : 0 ≤ B) (hΔ : 3 ≤ Δ)
    (htri : ∀ {U : Type u} [Fintype U] (H : SimpleGraph U) (w : U → ℝ),
      IsOptimizer H w → H.CliqueFree (k+2) → triangleMass H w ≤ B * edgeMass H w)
    (G : SimpleGraph V) (hf : G.CliqueFree (k+2)) (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) :
    ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧
      ∀ q : V → ℝ, (∀ v, 0 ≤ q v) →
        potential G q ≤ ((3+3*B/2)*Real.log Δ) * (I.card : ℝ) := by sorry
