-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_optimizer_cross_bound
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.optimizer_cross_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:28:45.010865+00:00
-- url     : https://prove2.me/theorems/7c3a6e34-0bfc-4454-8956-07d4ac9773fa
-- title:
--   Cross-mass bound for potential maximizers of $K_{k+2}$-free graphs
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$, with adjacency $u\sim v$. For $y:V\to\mathbb R$ let $E_G(y)=\sum_{\{u,v\}\in E(G)}y_uy_v$; a weight $w:V\to\mathbb R$ is an *optimizer* if $w\ge0$ and $w$ maximizes $\Phi_G(q)=\sum_vq_v(1-\log q_v)-E_G(q)$ over all $q:V\to[0,\infty)$ (with $0\log0=0$). For $A,B\subseteq V$ let $w(A)=\sum_{v\in A}w_v$ and $e_w(A,B)=\sum_{u\in A}\sum_{v\in B,\,u\sim v}w_uw_v$, and for $x\in\mathbb R$ let $g_x(s)=s\,(x+\max\{0,\log(1/s)\})$ for $s>0$ and $g_x(0)=0$.
--
--   Let $k\in\mathbb N$, assume that $G$ contains no clique on $k+2$ vertices, and let $w$ be an optimizer. Then for every real $x\ge1$ and all sets $A,B\subseteq V$, not necessarily disjoint, with $w(A)\le e^x$ and $w(B)\le e^x$,
--
--   $$
--   e_w(A,B)\le16\,(k+2)^2\,g_x\big(w(A)\big).
--   $$
--
--   In other words, $w$ has the *cross-mass property* with constant $C=16(k+2)^2$. This is the input from clique-freeness and optimality that the triangle-counting argument needs: from it one bounds the weighted triangle mass of an optimizer by a constant multiple of its edge mass, which leads to the logarithmic lower bound on the independence number of $K_r$-free graphs.
--
--   **Formalization Note** The conclusion is `CrossBound G w (16*((k:ℝ)+2)^2)`, which unfolds to the displayed inequality for all real `x ≥ 1` and all finsets `A B`; $g_x$ is `growth x`, and the clique hypothesis is `G.CliqueFree (k+2)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/CrossBound.lean#L95-L123

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

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u
variable {V : Type u} [Fintype V]

theorem OAI.CliqueFreeIndependence.WeightedGraph.optimizer_cross_bound (k : ℕ) (G : SimpleGraph V) {w : V → ℝ}
    (hw : IsOptimizer G w) (hfree : G.CliqueFree (k+2)) :
    CrossBound G w (16*((k:ℝ)+2)^2) := by sorry
