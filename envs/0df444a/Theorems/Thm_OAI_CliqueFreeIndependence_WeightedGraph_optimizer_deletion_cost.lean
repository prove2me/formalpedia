-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_optimizer_deletion_cost
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.optimizer_deletion_cost
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T21:21:13.983616+00:00
-- url     : https://prove2.me/theorems/fb254498-9772-45c9-ad5e-aa5045dd3efc
-- title:
--   Exact cost of deleting a vertex set from an optimizer: $\Phi_G(w)-\Phi_G(\mathbf 1_{V\setminus A}w)=w(A)+E_G(\mathbf 1_Aw)$
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$ (no loops, so $u\sim v$ implies $u\ne v$), and write $N(v)$ for the set of neighbours of a vertex $v$. For a weight function $w:V\to\mathbb{R}$ and $S\subseteq V$ put $w(S)=\sum_{v\in S}w_v$, and let $N_v(w)=w(N(v))=\sum_{u\sim v}w_u$ be the neighbour mass of $v$. The edge mass of $w$ is
--   $E_G(w)=\tfrac12\sum_{u\in V}\sum_{v\in V}\mathbf 1[u\sim v]\,w_uw_v=\sum_{\{u,v\}\in E(G)}w_uw_v,$
--   and the potential of $w$ is
--   $\Phi_G(w)=\sum_{v\in V}\varphi(w_v)-E_G(w)$, where $\varphi(t)=t\,(1-\log t)$ ($\log$ is the natural logarithm) and $\varphi(0)=0$. A weight function $w$ is called an *optimizer* for $G$ if $w_v\ge0$ for every $v$ and $\Phi_G(q)\le\Phi_G(w)$ for every $q:V\to\mathbb{R}$ with $q_v\ge0$ for all $v$; that is, $w$ maximizes $\Phi_G$ over the nonnegative orthant. For $S\subseteq V$ let $\mathbf 1_Sw$ be the restriction of $w$ to $S$, equal to $w_v$ for $v\in S$ and to $0$ otherwise.
--
--   If $w$ is an optimizer for $G$, then for every set $A\subseteq V$
--
--   $$
--   \Phi_G(w)-\Phi_G\bigl(\mathbf 1_{V\setminus A}w\bigr)=w(A)+E_G\bigl(\mathbf 1_Aw\bigr).
--   $$
--
--   So setting the weights on $A$ to zero lowers the potential of an optimizer by exactly the weight of $A$ plus the edge mass inside $A$. Applied to a closed neighbourhood $A=\{v\}\cup N(v)$, it measures the loss of potential when $v$ is put into an independent set and its neighbourhood is removed, the basic step of the greedy lower bound on the independence number.
--
--   **Formalization Note** The edge mass is `edgeMass G w = crossMass G w univ univ / 2`, the vertex summand is `vertexPotential t = t * (1 - Real.log t)` (Lean's convention $\log 0=0$ makes it vanish at $t=0$), the potential is `potential G w`, and `IsOptimizer G w` is the maximality property described above, quantified over all nonnegative real-valued functions on $V$. The restriction is `restrict`, and $V\setminus A$ is the complement `Aᶜ` of the finite set $A$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/Deletion.lean#L62-L89

import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
variable {V : Type u} [Fintype V]

theorem OAI.CliqueFreeIndependence.WeightedGraph.optimizer_deletion_cost {G : SimpleGraph V} {w : V → ℝ}
    (hw : IsOptimizer G w) (A : Finset V) :
    potential G w - potential G (restrict Aᶜ w) =
      mass w A + edgeMass G (restrict A w) := by sorry
