-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_weighted_splitting
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.weighted_splitting
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:02:05.443051+00:00
-- url     : https://prove2.me/theorems/11b66838-0fe6-4c61-914c-aa27435c8329
-- title:
--   Weighted vertex splitting lowers neighbour masses from $e^{x}$ to $e^{\sqrt{x}}$ at relative triangle cost $\kappa(C)\log x/\sqrt{x}$
-- statement:
--   Let $G$ be a finite simple graph on a finite vertex set $V$, write $u\sim v$ for adjacency and $N(u)=\{v\in V: u\sim v\}$ for the neighbourhood of $u$, and let $w\colon V\to\mathbb{R}$ be a vertex weight. For $A\subseteq V$ put $w(A)=\sum_{v\in A}w_v$. The neighbour mass, common-neighbour mass, edge mass and triangle mass are
--   $$
--   d_w(u)=w\big(N(u)\big),\qquad c_w(u,v)=w\big(N(u)\cap N(v)\big),\qquad E_G(w)=\frac12\sum_{u\sim v}w_uw_v,\qquad T_G(w)=\frac16\sum_{u\in V}w_u\sum_{v\in N(u)}w_v\,c_w(u,v),
--   $$
--   where $\sum_{u\sim v}$ runs over ordered pairs of adjacent vertices. Thus $E_G(w)=\sum_{\{u,v\}\in E(G)}w_uw_v$, and $T_G(w)$ is the sum of $w_uw_vw_z$ over the unordered triangles $\{u,v,z\}$ of $G$. For another graph $H$ (on any finite vertex set) and a weight $\tilde w$ on its vertices, $d^H_{\tilde w}$, $c^H_{\tilde w}$, $E_H(\tilde w)$, $T_H(\tilde w)$ denote the same quantities computed in $H$.
--
--   For a real constant $C$, the pair $(G,w)$ satisfies the cross-mass bound $\mathrm{CB}(G,w,C)$ if for every real $y\ge1$ and all sets $A,B\subseteq V$ (which may overlap) with $w(A)\le e^{y}$ and $w(B)\le e^{y}$,
--   $$
--   \sum_{u\in A}\sum_{v\in B,\ v\sim u}w_uw_v\;\le\;C\,g_y\big(w(A)\big),\qquad g_y(s)=s\,\Big(y+\max\big\{0,\log(1/s)\big\}\Big).
--   $$
--
--   For $C\ge1$ put
--   $$
--   \kappa(C)=6\Big(2\sqrt{\eta(C)+1}+\eta(C)+1\Big),\qquad \eta(C)=10+42C^2+2C.
--   $$
--
--   Assume that $G$ has at least one edge and $w_u>0$ for every $u\in V$. Let $C\ge1$ and $x\ge32$ be real numbers such that $\mathrm{CB}(G,w,C)$ holds, $c_w(u,v)\ge1/x$ for every edge $uv$ of $G$, and $d_w(u)\le e^{x}$ for every $u\in V$. Let $\vec E$ be the set of oriented edges $(u,v)$ of $G$, with source map $s(u,v)=u$. Then there is a simple graph $H$ on the vertex set $\vec E$, with vertex weights $w\circ s$, such that:
--
--   1. $s$ is an edge projection from $H$ to $G$: adjacent vertices of $H$ have adjacent sources in $G$, and an oriented edge $(y,z)$ of $H$ is determined by the pair $(s(y),s(z))$;
--   2. $d^H_{w\circ s}(y)\le e^{\sqrt x}$ for every $y\in\vec E$;
--   3. the triangle mass is almost preserved:
--   $$
--   \Big(1-\kappa(C)\,\frac{\log x}{\sqrt x}\Big)\,T_G(w)\le T_H(w\circ s).
--   $$
--
--   A single splitting replaces the bound $e^{x}$ on all neighbour masses by $e^{\sqrt x}$, while losing only the fraction $\kappa(C)\log x/\sqrt x$ of the weighted triangle count. Because the source map is an edge projection, the edge mass does not increase and the cross-mass bound passes to $H$. The step can therefore be iterated along the scales $x,\sqrt x,x^{1/4},\dots$, which is how triangle mass is bounded linearly by edge mass for cross-bounded weightings.
--
--   **Formalization Note** `CrossBound G w C` is $\mathrm{CB}(G,w,C)$, with $g_y$ given by `growth y s`; since Lean sets $1/0=0$ and $\log0=0$, one has $g_y(0)=0$. The constant $\kappa(C)$ is `splittingConstant C`, assembled from `smoothingConstant`, `entropyConstant` and `exceptionalConstant` as above. The hypothesis `Nonempty (EdgeState G)` says that $G$ has an edge.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/VertexSplitting.lean#L49-L86

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

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
variable {V : Type u} [Fintype V]
attribute [local instance 10000] edgeStateDecEq

theorem OAI.CliqueFreeIndependence.WeightedGraph.weighted_splitting {G : SimpleGraph V} [Nonempty (EdgeState G)] {w : V → ℝ}
    (hw : ∀ u, 0 < w u) {C x : ℝ} (hC : 1 ≤ C) (hCross : CrossBound G w C)
    (hx : 32 ≤ x) (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x) :
    ∃ H : SimpleGraph (EdgeState G), EdgeProjection H G EdgeState.src ∧
      (∀ z, neighborMass H (w ∘ EdgeState.src) z ≤ Real.exp (Real.sqrt x)) ∧
      (1 - splittingConstant C * (Real.log x / Real.sqrt x)) * triangleMass G w ≤
        triangleMass H (w ∘ EdgeState.src) := by sorry
