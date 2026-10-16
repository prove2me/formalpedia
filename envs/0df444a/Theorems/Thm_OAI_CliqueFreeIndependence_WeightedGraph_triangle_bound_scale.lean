-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_triangle_bound_scale
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.triangle_bound_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:07:53.203477+00:00
-- url     : https://prove2.me/theorems/a0096665-b023-49a7-8f4a-68320b0ae57b
-- title:
--   Triangle mass is at most $(1+e^{X}/3)(2-2^{-n})$ times edge mass at neighbour-mass level $\exp(X^{2^n})$
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
--   For $C\ge1$ put
--   $$
--   \kappa(C)=6\Big(2\sqrt{\eta(C)+1}+\eta(C)+1\Big),\qquad \eta(C)=10+42C^2+2C.
--   $$
--
--   Let $C\ge1$ and $X\ge32$ be real numbers with $\kappa(C)\,\log X/\sqrt X\le\frac14$, and let $n\in\mathbb{N}$. Then for every finite simple graph $G$ on a finite vertex set $V$ and every weight $w$ such that $w_u>0$ for all $u$, $\mathrm{CB}(G,w,C)$ holds, and $d_w(u)\le\exp\big(X^{2^{n}}\big)$ for every $u\in V$,
--   $$
--   T_G(w)\le\Big(1+\frac{e^{X}}{3}\Big)\Big(2-\frac1{2^{n}}\Big)\,E_G(w).
--   $$
--
--   The factor $2-2^{-n}$ stays below $2$, so $T_G(w)\le2(1+e^{X}/3)\,E_G(w)$ holds uniformly at every neighbour-mass level $\exp(X^{2^n})$. The levels $X,X^2,X^4,\dots$ are those traversed by repeated square-root reductions, and the uniformity in $n$ is what makes the final triangle bound independent of the size of the graph.
--
--   **Formalization Note** $X^{2^n}$ is `Numerical.scale X n`, defined recursively by $\mathrm{scale}(X,0)=X$ and $\mathrm{scale}(X,n+1)=\mathrm{scale}(X,n)^2$, and $\log X/\sqrt X$ is `Numerical.lossRatio X`. The statement about graphs is quantified over all finite vertex types in a fixed universe, after $C$, $X$ and $n$ are fixed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/TriangleBound.lean#L78-L138

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

theorem OAI.CliqueFreeIndependence.WeightedGraph.triangle_bound_scale {C X : ℝ} (hC : 1 ≤ C) (hX : 32 ≤ X)
    (hsmall : splittingConstant C * Numerical.lossRatio X ≤ 1/4) (n : ℕ) :
    ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (w : V → ℝ),
      (∀ u, 0 < w u) → CrossBound G w C →
      (∀ u, neighborMass G w u ≤ Real.exp (Numerical.scale X n)) →
      triangleMass G w ≤ (1+Real.exp X/3) * (2-(1/2:ℝ)^n) * edgeMass G w := by sorry
