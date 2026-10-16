-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_TriangleState_sum_eq
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.TriangleState.sum_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:31:05.776513+00:00
-- url     : https://prove2.me/theorems/e8827905-3829-46fd-9bef-2980509733b6
-- title:
--   Sums over ordered triangles as iterated neighborhood sums
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$, with adjacency $u\sim v$ and neighborhoods $N(u)=\{v\in V:u\sim v\}$. An *ordered triangle* of $G$ is a triple $(u,v,z)\in V^3$ with $u\sim v$, $u\sim z$ and $v\sim z$, so that every triangle of $G$ gives $6$ ordered triangles; let $\mathcal T(G)$ be the finite set of ordered triangles. Then for every function $f:V\times V\times V\to\mathbb R$,
--
--   $$
--   \sum_{(u,v,z)\in\mathcal T(G)}f(u,v,z)=\sum_{u\in V}\ \sum_{v\in N(u)}\ \sum_{z\in N(u)}\mathbf 1[v\sim z]\,f(u,v,z).
--   $$
--
--   This bookkeeping identity converts sums over the finite type of ordered triangles into explicit neighborhood sums. It is used, for instance, to show that the total of $w_uw_vw_z$ over ordered triangles is six times the weighted triangle mass, and to compute edge marginals of triangle-weighted sums.
--
--   **Formalization Note** Ordered triangles form the subtype `TriangleState G` of `V × V × V`, with coordinates `first`, `second` and `third`; $N(u)$ is the finset `neighbors G u`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/TriangleState.lean#L82-L101

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

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph OAI.CliqueFreeIndependence.WeightedGraph.TriangleState
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
variable {V : Type u} [Fintype V]
attribute [local instance 10000] edgeStateDecEq
variable {G : SimpleGraph V}

theorem OAI.CliqueFreeIndependence.WeightedGraph.TriangleState.sum_eq (f : V → V → V → ℝ) :
    (∑ t : TriangleState G, f t.first t.second t.third) =
      ∑ u, ∑ v ∈ neighbors G u, ∑ z ∈ neighbors G u,
        if G.Adj v z then f u v z else 0 := by sorry
