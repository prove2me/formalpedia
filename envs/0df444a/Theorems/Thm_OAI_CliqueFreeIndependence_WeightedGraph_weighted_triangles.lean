-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_weighted_triangles
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.weighted_triangles
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:09:44.000402+00:00
-- url     : https://prove2.me/theorems/78d6bfa0-1b35-4abc-8d25-f6f516dd142e
-- title:
--   Cross-bounded positive weightings have triangle mass at most a constant times edge mass
-- statement:
--   Let $G$ be a finite simple graph on a finite vertex set $V$, write $u\sim v$ for adjacency and $N(u)=\{v\in V: u\sim v\}$ for the neighbourhood of $u$, and let $w\colon V\to\mathbb{R}$ be a vertex weight. For $A\subseteq V$ put $w(A)=\sum_{v\in A}w_v$. The neighbour mass, common-neighbour mass, edge mass and triangle mass are
--   $$
--   d_w(u)=w\big(N(u)\big),\qquad c_w(u,v)=w\big(N(u)\cap N(v)\big),\qquad E_G(w)=\frac12\sum_{u\sim v}w_uw_v,\qquad T_G(w)=\frac16\sum_{u\in V}w_u\sum_{v\in N(u)}w_v\,c_w(u,v),
--   $$
--   where $\sum_{u\sim v}$ runs over ordered pairs of adjacent vertices. Thus $E_G(w)=\sum_{\{u,v\}\in E(G)}w_uw_v$, and $T_G(w)$ is the sum of $w_uw_vw_z$ over the unordered triangles $\{u,v,z\}$ of $G$.
--
--   For a real constant $C$, the pair $(G,w)$ satisfies the cross-mass bound $\mathrm{CB}(G,w,C)$ if for every real $y\ge1$ and all sets $A,B\subseteq V$ (which may overlap) with $w(A)\le e^{y}$ and $w(B)\le e^{y}$,
--   $$
--   \sum_{u\in A}\sum_{v\in B,\ v\sim u}w_uw_v\;\le\;C\,g_y\big(w(A)\big),\qquad g_y(s)=s\,\Big(y+\max\big\{0,\log(1/s)\big\}\Big).
--   $$
--
--   Let $C\ge1$. Then there is a constant $B>0$, depending only on $C$, such that for every finite simple graph $G$ on a finite vertex set $V$ and every weight $w\colon V\to\mathbb{R}$ with $w_v>0$ for all $v$ that satisfies $\mathrm{CB}(G,w,C)$,
--   $$
--   T_G(w)\le B\,E_G(w).
--   $$
--
--   The cross-mass bound limits the weighted number of edges between two sets of weight at most $e^{y}$ by $C\,g_y$ of the weight of the first set. The theorem turns this into a linear bound of the weighted triangle count by the weighted edge count, with a constant that does not depend on the number of vertices or on the total weight. In the clique-free application, the cross-mass bound is established for maximisers of a variational potential on $K_r$-free graphs. This theorem then supplies the triangle hypothesis $T\le B\,E$ for the maximum-degree independence argument.
--
--   **Formalization Note** The statement quantifies over all finite vertex types in a fixed universe, and $B$ is chosen before the graph. In `growth y s` the conventions $1/0=0$ and $\log0=0$ give $g_y(0)=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/TriangleBound.lean#L140-L161

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
universe u
variable {V : Type u} [Fintype V]

theorem OAI.CliqueFreeIndependence.WeightedGraph.weighted_triangles {C : ℝ} (hC : 1 ≤ C) :
    ∃ B : ℝ, 0 < B ∧ ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (w : V → ℝ),
      (∀ v, 0 < w v) → CrossBound G w C → triangleMass G w ≤ B * edgeMass G w := by sorry
