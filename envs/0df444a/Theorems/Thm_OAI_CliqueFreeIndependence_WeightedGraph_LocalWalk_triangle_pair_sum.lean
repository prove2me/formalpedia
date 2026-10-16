-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_LocalWalk_triangle_pair_sum
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.triangle_pair_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:48:19.094472+00:00
-- url     : https://prove2.me/theorems/89ca002b-aa55-4726-9df7-26f7f6fddfed
-- title:
--   Weighted ordered triangles as one step of the stationary local walk
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$ with at least one edge, and let $w:V\to\mathbb{R}$ satisfy $w(u)>0$ for all $u$. Write $N(u)$ for the neighbourhood of $u$, $W(u,v)=\sum_{z\in N(u)\cap N(v)}w(z)$, and $\vec E(G)$ for the set of oriented edges $(u,v)$ with $u\sim v$. An *ordered triangle* is a triple $(a,b,c)\in V^{3}$ of pairwise adjacent vertices; it has weight $w(a)w(b)w(c)$ and determines the two oriented edges $(a,b)$ and $(a,c)$ leaving its first vertex. The *local walk* $T$ on $\vec E(G)$ is given by $T\big((u,v),(u',v')\big)=w(v')/W(u,v)$ if $u'=u$ and $v\sim v'$, and $0$ otherwise; its *edge law* is $\pi(u,v)=w(u)w(v)W(u,v)/Z$, where $Z=\sum_{(u,v)\in\vec E(G)}w(u)w(v)W(u,v)$.
--
--   Assume that $W(u,v)>0$ for every edge $uv$. Then for every function $f:\vec E(G)\times\vec E(G)\to\mathbb{R}$,
--
--   $$
--   \sum_{\substack{(a,b,c)\in V^{3}\\ a\sim b,\ a\sim c,\ b\sim c}}w(a)\,w(b)\,w(c)\,f\big((a,b),(a,c)\big)\;=\;Z\sum_{e\in\vec E(G)}\pi(e)\sum_{z\in\vec E(G)}T(e,z)\,f(e,z).
--   $$
--
--   In words: drawing an oriented edge $e$ from $\pi$ and then one step $z$ of the local walk produces the corner pair $(a,b),(a,c)$ of an ordered triangle chosen with probability proportional to its weight, and $Z$ is the total weight of ordered triangles. This dictionary turns averages over weighted triangles, such as the triangle mass that survives a vertex splitting, into expectations along one step of the stationary local walk, and vice versa.
--
--   **Formalization Note** Ordered triangles form the type `TriangleState G`, with weight `TriangleState.weight w` and corner edges `t.edge12`, `t.edge13`; $T$, $\pi$ and $Z$ are `transition G w`, `law G w` and `normalizer G w`. The hypothesis that $G$ has an edge is the instance `[Nonempty (EdgeState G)]`, which guarantees $Z>0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/WalkCoupling.lean#L24-L43

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

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
variable {V : Type u} [Fintype V]
attribute [local instance 10000] edgeStateDecEq
open FiniteEntropy FiniteKernel
variable {G : SimpleGraph V} {w : V → ℝ}

theorem OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.triangle_pair_sum [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v)
    (f : EdgeState G → EdgeState G → ℝ) :
    (∑ t : TriangleState G, TriangleState.weight w t * f t.edge12 t.edge13) =
      normalizer G w * ∑ e, law G w e * ∑ z, transition G w e z * f e z := by sorry
