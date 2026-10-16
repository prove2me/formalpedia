-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_maximum_degree_independence
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.maximum_degree_independence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:14:42.969131+00:00
-- url     : https://prove2.me/theorems/8a8942bc-413f-4aa6-9daa-d2a643f76409
-- title:
--   Independence number of $K_{k+2}$-free graphs of maximum degree $\Delta$ is at least $|V|\log\Delta/(4(3+3B/2)\Delta)$
-- statement:
--   Let $G$ be a finite simple graph on a finite vertex set $V$. For a weight $q\colon V\to\mathbb{R}$ let $E_G(q)=\sum_{\{u,v\}\in E(G)}q_uq_v$ be its edge mass and $T_G(q)=\sum q_uq_vq_z$ its triangle mass, where the sum runs over the unordered triangles $\{u,v,z\}$ of $G$. Define the potential
--   $$
--   \Phi_G(q)=\sum_{v\in V}q_v\,(1-\log q_v)-E_G(q),
--   $$
--   with the convention $0\log0=0$. A weight $w$ is a maximiser for $G$ if $w_v\ge0$ for all $v$ and $\Phi_G(q)\le\Phi_G(w)$ for every $q$ with $q_v\ge0$ for all $v$. A graph is $K_{k+2}$-free if it contains no clique on $k+2$ vertices, and a set $I\subseteq V$ is independent if no two of its vertices are adjacent. The independence number $\alpha(G)$ is the largest size of an independent set of $G$.
--
--   Let $k\in\mathbb{N}$ and let $B\ge0$ and $\Delta\ge3$ be real numbers. Assume the triangle hypothesis: for every finite simple graph $H$ and every maximiser $w$ for $H$, if $H$ is $K_{k+2}$-free then $T_H(w)\le B\,E_H(w)$. Then every $K_{k+2}$-free graph $G$ on $V$ in which every vertex has degree at most $\Delta$ satisfies
--   $$
--   \alpha(G)\ge\frac{|V|\,\log\Delta}{4\,\big(3+\tfrac{3B}{2}\big)\,\Delta}.
--   $$
--
--   This is the bounded-degree form of the logarithmic independence bound. For $K_{k+2}$-free graphs of maximum degree at most $\Delta$ it gives $\alpha(G)\ge c\,|V|\log\Delta/\Delta$ with $c=1/(12+6B)$, which depends only on the triangle constant $B$. When the triangle hypothesis is available for some $B$, as provided by the weighted triangle theorem for cross-bounded weights, restricting to the vertices of degree at most twice the average degree turns this into an average-degree bound $\alpha(G)\ge c\,|V|\log d/d$ for $K_r$-free graphs.
--
--   **Formalization Note** `G.indepNum` is Mathlib's independence number, and the inequality is between real numbers, with $|V|$ being `Fintype.card V`. The triangle hypothesis quantifies over all finite vertex types in the same universe as $V$, and maximisers are `IsOptimizer`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/MaxDegree.lean#L69-L85

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

theorem OAI.CliqueFreeIndependence.WeightedGraph.maximum_degree_independence (k : ℕ) {B Δ : ℝ} (hB : 0 ≤ B) (hΔ : 3 ≤ Δ)
    (htri : ∀ {U : Type u} [Fintype U] (H : SimpleGraph U) (w : U → ℝ),
      IsOptimizer H w → H.CliqueFree (k+2) → triangleMass H w ≤ B * edgeMass H w)
    (G : SimpleGraph V) (hf : G.CliqueFree (k+2)) (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) :
    (Fintype.card V : ℝ)*Real.log Δ/(4*(3+3*B/2)*Δ) ≤ (G.indepNum : ℝ) := by sorry
