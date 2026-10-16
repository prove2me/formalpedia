-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_TriangleState_corner_sum
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.TriangleState.corner_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:32:20.694375+00:00
-- url     : https://prove2.me/theorems/55ceaa6e-9a9c-4295-8ae4-af3f937e9a05
-- title:
--   Ordered triangles as pairs of oriented edges with a common tail
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$, with adjacency $u\sim v$. An *oriented edge* is a pair $e=(e^-,e^+)$ of vertices with $e^-\sim e^+$ (tail $e^-$, head $e^+$); $\vec E(G)$ denotes the finite set of oriented edges. An *ordered triangle* is a triple $t=(a,b,c)$ with $a\sim b$, $a\sim c$ and $b\sim c$; $\mathcal T(G)$ is the set of ordered triangles, and $t_{12}=(a,b)$, $t_{13}=(a,c)$ are the two oriented edges of $t$ leaving its first vertex. For a weight $w:V\to\mathbb R$ let $w(t)=w_aw_bw_c$.
--
--   Then for every $w:V\to\mathbb R$ and every function $f:\vec E(G)\times\vec E(G)\to\mathbb R$,
--
--   $$
--   \sum_{t\in\mathcal T(G)}w(t)\,f(t_{12},t_{13})=\sum_{e\in\vec E(G)}\ \sum_{z\in\vec E(G)}\mathbf 1\big[e^-=z^-,\ e^+\sim z^+\big]\,w_{e^-}w_{e^+}w_{z^+}\,f(e,z).
--   $$
--
--   The identity identifies ordered triangles with corners: pairs of oriented edges with a common tail whose heads are adjacent. It is used to rewrite triangle-weighted sums of functions of the two edges at a corner as sums over pairs of oriented edges, and thereby as averages of a transition kernel on oriented edges against its stationary law.
--
--   **Formalization Note** Oriented edges are `EdgeState G` (with endpoints `src` and `dst`), ordered triangles are `TriangleState G`, $t_{12}$ and $t_{13}$ are `t.edge12` and `t.edge13`, and $w(t)$ is `TriangleState.weight w t`. No sign condition on $w$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/TriangleState.lean#L158-L173

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

theorem OAI.CliqueFreeIndependence.WeightedGraph.TriangleState.corner_sum (w : V → ℝ) (f : EdgeState G → EdgeState G → ℝ) :
    (∑ t : TriangleState G, weight w t * f t.edge12 t.edge13) =
      ∑ e : EdgeState G, ∑ z : EdgeState G,
        if e.src = z.src ∧ G.Adj e.dst z.dst
          then w e.src * w e.dst * w z.dst * f e z else 0 := by sorry
