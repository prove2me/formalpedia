-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_optimizer_cross_disjoint
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.optimizer_cross_disjoint
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:27:10.901832+00:00
-- url     : https://prove2.me/theorems/0d81017f-e5a5-49a0-b173-f4d8fc7f4e66
-- title:
--   Cross mass from a clique-free set to a disjoint set at a potential maximizer
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$, with adjacency $u\sim v$. For $y:V\to\mathbb R$ let $E_G(y)=\sum_{\{u,v\}\in E(G)}y_uy_v$, and call $w:V\to\mathbb R$ an *optimizer* if $w\ge0$ and $w$ maximizes the potential $\Phi_G(q)=\sum_vq_v(1-\log q_v)-E_G(q)$ over all $q:V\to[0,\infty)$ (with $0\log0=0$). For $A,B\subseteq V$ put $w(A)=\sum_{v\in A}w_v$ and $e_w(A,B)=\sum_{u\in A}\sum_{v\in B,\,u\sim v}w_uw_v$. For $x\in\mathbb R$ define the growth function
--
--   $$
--   g_x(s)=s\,\big(x+\max\{0,\log(1/s)\}\big)\quad(s>0),\qquad g_x(0)=0 .
--   $$
--
--   Let $k\in\mathbb N$, let $w$ be an optimizer, and let $S,D\subseteq V$ be disjoint sets such that $S$ contains no clique of $G$ on $k+2$ vertices. If $x\ge1$, $w(S)\le e^x$ and $w(D)\le e^x$, then
--
--   $$
--   e_w(S,D)\le4\,(k+2)^2\,g_x\big(w(S)\big).
--   $$
--
--   For $w(S)\ge1$ the right-hand side is $4(k+2)^2x\,w(S)$, and for small $w(S)$ it carries the extra factor $\log(1/w(S))$. This is the disjoint-sets case of the cross-mass property of optimizers of $K_{k+2}$-free graphs; averaging over random two-colourings removes the disjointness assumption.
--
--   **Formalization Note** $g_x$ is `growth x`, defined for all real $s$ as `s * (x + max 0 (Real.log (1 / s)))`, which vanishes at $s=0$. The clique hypothesis is `G.CliqueFreeOn S (k+2)`, the optimizer hypothesis is `IsOptimizer G w`, and $e_w(S,D)$ is `crossMass G w S D`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/DisjointCross.lean#L108-L151

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

theorem OAI.CliqueFreeIndependence.WeightedGraph.optimizer_cross_disjoint (k : ℕ) (G : SimpleGraph V) {w : V → ℝ}
    (hw : IsOptimizer G w) (S D : Finset V) (hSD : Disjoint S D)
    (hfree : G.CliqueFreeOn (↑S) (k+2)) {x : ℝ} (hx : 1 ≤ x)
    (hsup : mass w S ≤ Real.exp x) (htup : mass w D ≤ Real.exp x) :
    crossMass G w S D ≤ (4*((k:ℝ)+2)^2)*growth x (mass w S) := by sorry
