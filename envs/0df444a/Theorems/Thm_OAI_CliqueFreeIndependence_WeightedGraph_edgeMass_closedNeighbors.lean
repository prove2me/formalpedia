-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_edgeMass_closedNeighbors
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.edgeMass_closedNeighbors
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T21:20:25.630823+00:00
-- url     : https://prove2.me/theorems/34334cac-a2b4-457e-a60d-24341bc536ff
-- title:
--   Edge mass inside a closed neighbourhood: $E_G(\mathbf 1_{N[v]}w)=w_vN_v(w)+\tfrac12T_v(w)$
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$, let $w:V\to\mathbb{R}$ be a real weight function, and let $v\in V$. Write $N(v)$ for the neighbourhood of $v$, $N[v]=\{v\}\cup N(v)$ for its closed neighbourhood, $w(S)=\sum_{u\in S}w_u$, and $N_v(w)=w(N(v))$ for the neighbour mass of $v$. Let $\mathbf 1_Sw$ denote the restriction of $w$ to $S$ (equal to $w$ on $S$ and to $0$ elsewhere), and $E_G(x)=\sum_{\{u,u'\}\in E(G)}x_ux_{u'}$ the edge mass. Define the local triangle mass at $v$ by
--   $T_v(w)=\sum_{u\in N(v)}w_u\,w\bigl(N(v)\cap N(u)\bigr)=\sum_{u\in N(v)}\sum_{x\in N(v)}\mathbf 1[u\sim x]\,w_uw_x$, which counts each triangle $\{v,u,x\}$ through $v$ twice, with weight $w_uw_x$. Then
--
--   $$
--   E_G\bigl(\mathbf 1_{N[v]}w\bigr)=w_v\,N_v(w)+\frac{T_v(w)}{2}.
--   $$
--
--   The two terms correspond to the edges from $v$ to its neighbours and to the edges inside $N(v)$. Combined with the deletion-cost identity for optimizers, this expresses the cost of removing a closed neighbourhood in terms of neighbour masses and local triangle masses, which is how triangle counts enter the bound on the independence number.
--
--   **Formalization Note** In Lean $N[v]$ is `closedNeighbors G v`, the restriction is `restrict`, $N_v(w)$ is `neighborMass G w v`, and $T_v(w)$ is `triangleAt G w v`, defined via `commonMass G w v u` $=w(N(v)\cap N(u))$. The weight function $w$ is arbitrary.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/Deletion.lean#L33-L60

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

theorem OAI.CliqueFreeIndependence.WeightedGraph.edgeMass_closedNeighbors (G : SimpleGraph V) (w : V → ℝ) (v : V) :
    edgeMass G (restrict (closedNeighbors G v) w) =
      w v * neighborMass G w v + triangleAt G w v / 2 := by sorry
