-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_peeling
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.peeling
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:02:55.34606+00:00
-- url     : https://prove2.me/theorems/03f4a26d-af7c-4851-84a0-6b2299b5a4f8
-- title:
--   Peeling edges of small common-neighbour mass loses at most $\tau$ times the edge mass in triangles
-- statement:
--   Let $G$ be a finite simple graph on a finite vertex set $V$, write $u\sim v$ for adjacency and $N(u)=\{v\in V: u\sim v\}$ for the neighbourhood of $u$, and let $w\colon V\to\mathbb{R}$ be a vertex weight. For $A\subseteq V$ put $w(A)=\sum_{v\in A}w_v$. The neighbour mass, common-neighbour mass, edge mass and triangle mass are
--   $$
--   d_w(u)=w\big(N(u)\big),\qquad c_w(u,v)=w\big(N(u)\cap N(v)\big),\qquad E_G(w)=\frac12\sum_{u\sim v}w_uw_v,\qquad T_G(w)=\frac16\sum_{u\in V}w_u\sum_{v\in N(u)}w_v\,c_w(u,v),
--   $$
--   where $\sum_{u\sim v}$ runs over ordered pairs of adjacent vertices. Thus $E_G(w)=\sum_{\{u,v\}\in E(G)}w_uw_v$, and $T_G(w)$ is the sum of $w_uw_vw_z$ over the unordered triangles $\{u,v,z\}$ of $G$. For a graph $H$ on the same vertex set we write $c^H_w$, $E_H(w)$ and $T_H(w)$ for the quantities computed in $H$.
--
--   Let $w_v>0$ for every $v\in V$ and let $\tau>0$. Then there is a subgraph $H\le G$ on the same vertex set (every edge of $H$ is an edge of $G$) such that:
--
--   1. every edge of $H$ has common-neighbour mass at least $\tau$ in $H$, that is, $c^H_w(u,v)\ge\tau$ whenever $u\sim_Hv$;
--   2. the triangle mass drops by at most $\tau$ times the edge mass of $G$:
--   $$
--   T_G(w)-\tau\,E_G(w)\le T_H(w).
--   $$
--
--   So edges that lie in little triangle weight can be deleted at a cost to $T$ that is small compared with $E$. The lower bound $c^H_w\ge\tau$ makes the local random walk on the oriented edges of $H$ (from $(u,v)$ to $(u,z)$, with $z$ a common neighbour of $u$ and $v$) well defined, with transition probabilities $w_z/c^H_w(u,v)\le w_z/\tau$. With $\tau=1/x$ this is the preprocessing step that comes before vertex splitting.
--
--   **Formalization Note** $H\le G$ is the order on `SimpleGraph V`, and $c^H_w$, $E_H$, $T_H$ are `commonMass H w`, `edgeMass H w` and `triangleMass H w`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/Peeling.lean#L135-L157

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
universe u v
variable {V : Type u} [Fintype V]
attribute [local instance 10000] edgeStateDecEq
open FiniteCoupling

theorem OAI.CliqueFreeIndependence.WeightedGraph.peeling (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 < w v)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ H : SimpleGraph V, H ≤ G ∧
      (∀ u v, H.Adj u v → τ ≤ commonMass H w u v) ∧
      triangleMass G w - τ * edgeMass G w ≤ triangleMass H w := by sorry
