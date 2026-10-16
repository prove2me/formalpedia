-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_optimizer_edge_bound
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.optimizer_edge_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T21:17:48.974979+00:00
-- url     : https://prove2.me/theorems/9844d3af-9803-4add-bfb2-241729a7d06a
-- title:
--   An optimizer has edge mass at most $\tfrac12\log\Delta$ times its total weight
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$ (no loops, so $u\sim v$ implies $u\ne v$), and write $N(v)$ for the set of neighbours of a vertex $v$. For a weight function $w:V\to\mathbb{R}$ and $S\subseteq V$ put $w(S)=\sum_{v\in S}w_v$, and let $N_v(w)=w(N(v))=\sum_{u\sim v}w_u$ be the neighbour mass of $v$. The edge mass of $w$ is
--   $E_G(w)=\tfrac12\sum_{u\in V}\sum_{v\in V}\mathbf 1[u\sim v]\,w_uw_v=\sum_{\{u,v\}\in E(G)}w_uw_v,$
--   and the potential of $w$ is
--   $\Phi_G(w)=\sum_{v\in V}\varphi(w_v)-E_G(w)$, where $\varphi(t)=t\,(1-\log t)$ ($\log$ is the natural logarithm) and $\varphi(0)=0$. A weight function $w$ is called an *optimizer* for $G$ if $w_v\ge0$ for every $v$ and $\Phi_G(q)\le\Phi_G(w)$ for every $q:V\to\mathbb{R}$ with $q_v\ge0$ for all $v$; that is, $w$ maximizes $\Phi_G$ over the nonnegative orthant.
--
--   Assume that $V$ is nonempty, that $\Delta\ge3$ is a real number, and that every vertex has degree $\deg_G(v)\le\Delta$. If $w$ is an optimizer for $G$, then
--
--   $$
--   2\,E_G(w)\le\log\Delta\cdot\sum_{v\in V}w_v .
--   $$
--
--   For an optimizer one has $2E_G(w)=\sum_vw_vN_v(w)=\sum_vw_v\log(1/w_v)$, so the inequality says that the $w$-weighted average of $\log(1/w_v)$ is at most $\log\Delta$. It bounds the average cost of removing closed neighbourhoods in the greedy construction of large independent sets in graphs of maximum degree at most $\Delta$.
--
--   **Formalization Note** The edge mass is `edgeMass G w = crossMass G w univ univ / 2`, the vertex summand is `vertexPotential t = t * (1 - Real.log t)` (Lean's convention $\log 0=0$ makes it vanish at $t=0$), the potential is `potential G w`, and `IsOptimizer G w` is the maximality property described above, quantified over all nonnegative real-valued functions on $V$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/OptimizerBounds.lean#L81-L112

import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
variable {V : Type u} [Fintype V]

theorem OAI.CliqueFreeIndependence.WeightedGraph.optimizer_edge_bound {G : SimpleGraph V} {w : V → ℝ} (hw : IsOptimizer G w)
    [Nonempty V] {Δ : ℝ} (hΔ : 3 ≤ Δ) (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) :
    2 * edgeMass G w ≤ Real.log Δ * (∑ v, w v) := by sorry
