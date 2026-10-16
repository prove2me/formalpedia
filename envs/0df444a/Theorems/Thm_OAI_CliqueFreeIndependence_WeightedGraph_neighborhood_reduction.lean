-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_neighborhood_reduction
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.neighborhood_reduction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:06:31.468721+00:00
-- url     : https://prove2.me/theorems/3b31a73d-7eea-4bb4-b2ad-ffeda09fddeb
-- title:
--   One reduction round: neighbour masses from $e^{x}$ to $e^{\sqrt{x}}$ by peeling and vertex splitting
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
--   For a graph $J$ on a finite set $U$ and a map $\pi\colon U\to V$, we say that $\pi$ is an edge projection from $J$ to $G$ if (i) $a\sim_J b$ implies $\pi(a)\sim_G\pi(b)$, and (ii) $\pi$ is injective on oriented edges: whenever $a\sim_J b$, $a'\sim_J b'$, $\pi(a)=\pi(a')$ and $\pi(b)=\pi(b')$, then $a=a'$ and $b=b'$. The vertices of $J$ carry the pulled-back weight $w\circ\pi$, so each $a\in U$ is a weighted copy of $\pi(a)$.
--
--   Let $w_u>0$ for every $u\in V$, let $C\ge1$ be such that $\mathrm{CB}(G,w,C)$ holds, and let $x\ge32$ be such that
--   $$
--   \varepsilon:=\kappa(C)\,\frac{\log x}{\sqrt x}\le1
--   $$
--   and $d_w(u)\le e^{x}$ for every $u\in V$. Then there exist a finite set $U$, a simple graph $J$ on $U$ and a map $\pi\colon U\to V$ such that $\pi$ is an edge projection from $J$ to $G$, $d^J_{w\circ\pi}(a)\le e^{\sqrt x}$ for every $a\in U$, and
--   $$
--   (1-\varepsilon)\,T_G(w)-\frac{E_G(w)}{x}\le T_J(w\circ\pi).
--   $$
--
--   This is one round of the reduction behind the weighted triangle bound. The exponent that controls all neighbour masses drops from $x$ to $\sqrt x$, at the price of a relative triangle loss $\varepsilon$ and an additive loss $E_G(w)/x$. Edge projections do not increase edge mass and transfer the cross-mass bound to $(J,w\circ\pi)$, so the step can be repeated on $J$.
--
--   **Formalization Note** The copy set $U$ is an existentially quantified type in the same universe as $V$, together with a `Fintype` instance. The quantity $\varepsilon$ is `splittingConstant C * Numerical.lossRatio x`, where `lossRatio x` is $\log x/\sqrt x$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/TriangleBound.lean#L32-L76

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

theorem OAI.CliqueFreeIndependence.WeightedGraph.neighborhood_reduction (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ u, 0 < w u)
    {C x : ℝ} (hC : 1 ≤ C) (hCross : CrossBound G w C) (hx : 32 ≤ x)
    (hε : splittingConstant C * Numerical.lossRatio x ≤ 1)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x) :
    ∃ (U : Type u) (_ : Fintype U) (J : SimpleGraph U) (π : U → V),
      EdgeProjection J G π ∧ (∀ a, neighborMass J (w ∘ π) a ≤ Real.exp (Real.sqrt x)) ∧
      (1-splittingConstant C * Numerical.lossRatio x) * triangleMass G w - edgeMass G w / x ≤
        triangleMass J (w ∘ π) := by sorry
