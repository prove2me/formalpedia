-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_Splitting_exists_graph
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.Splitting.exists_graph
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:59:12.027397+00:00
-- url     : https://prove2.me/theorems/0848e075-3e95-4a31-a7fd-325b8d0004ae
-- title:
--   Vertex splitting along a source-preserving kernel with neighbour masses at most $e^{a}$ and controlled triangle loss
-- statement:
--   Let $G$ be a finite simple graph on a finite vertex set $V$, write $u\sim v$ for adjacency and $N(u)=\{v\in V: u\sim v\}$ for the neighbourhood of $u$, and let $w\colon V\to\mathbb{R}$ be a vertex weight. For $A\subseteq V$ put $w(A)=\sum_{v\in A}w_v$. The neighbour mass, common-neighbour mass, edge mass and triangle mass are
--   $$
--   d_w(u)=w\big(N(u)\big),\qquad c_w(u,v)=w\big(N(u)\cap N(v)\big),\qquad E_G(w)=\frac12\sum_{u\sim v}w_uw_v,\qquad T_G(w)=\frac16\sum_{u\in V}w_u\sum_{v\in N(u)}w_v\,c_w(u,v),
--   $$
--   where $\sum_{u\sim v}$ runs over ordered pairs of adjacent vertices. Thus $E_G(w)=\sum_{\{u,v\}\in E(G)}w_uw_v$, and $T_G(w)$ is the sum of $w_uw_vw_z$ over the unordered triangles $\{u,v,z\}$ of $G$. For another graph $H$ (on any finite vertex set) and a weight $\tilde w$ on its vertices, $d^H_{\tilde w}$, $c^H_{\tilde w}$, $E_H(\tilde w)$, $T_H(\tilde w)$ denote the same quantities computed in $H$.
--
--   Assume that $G$ has at least one edge, that $w_u>0$ for every $u\in V$, and that $c_w(u,v)>0$ for every edge $uv$. Let $\vec E$ be the finite set of oriented edges $e=(u,v)$ of $G$, with source $s(e)=u$ and target $t(e)=v$. The local walk is the kernel on $\vec E$ given by
--   $$
--   P(e,f)=\begin{cases}\dfrac{w_{t(f)}}{c_w\big(s(e),t(e)\big)}, & \text{if } s(f)=s(e)\text{ and }t(e)\sim t(f),\\ 0, & \text{otherwise};\end{cases}
--   $$
--   from $(u,v)$ it moves to $(u,z)$, where $z$ is a common neighbour of $u$ and $v$ chosen with probability proportional to $w_z$. Its normaliser and stationary law are
--   $$
--   Z=\sum_{e\in\vec E}w_{s(e)}\,w_{t(e)}\,c_w\big(s(e),t(e)\big),\qquad \lambda(e)=\frac{w_{s(e)}\,w_{t(e)}\,c_w\big(s(e),t(e)\big)}{Z}.
--   $$
--   For vectors $p,p'$ indexed by $\vec E$, $\mathrm{tv}(p,p')=\frac12\sum_{y}|p_y-p'_y|$ is the total variation distance, and $K(e,\cdot)$ denotes the row of a matrix $K$ indexed by $e$.
--
--   Let $K=(K(e,y))_{e,y\in\vec E}$ be a stochastic matrix (nonnegative entries, every row summing to $1$) that never changes the source: $K(e,z)=0$ whenever $s(e)\neq s(z)$. Let $a,D,\delta$ be real numbers such that
--   $$
--   \sum_{e\in\vec E}\lambda(e)\sum_{z\in\vec E}P(e,z)\,\mathrm{tv}\big(K(e,\cdot),K(z,\cdot)\big)\le D,\qquad\sum_{e\in\vec E}\lambda(e)\sum_{y\in\vec E:\ K(y,e)<w_{t(e)}e^{-a}}K(e,y)\le\delta.
--   $$
--   Then there is a simple graph $H$ with vertex set $\vec E$ such that, giving each vertex $y$ of $H$ the weight $(w\circ s)(y)=w_{s(y)}$, so that $y$ is a copy of $s(y)$, the following hold.
--
--   1. The source map is an edge projection from $H$ to $G$: $y\sim_Hz$ implies $s(y)\sim_Gs(z)$, and if $y\sim_Hz$, $y'\sim_Hz'$, $s(y)=s(y')$ and $s(z)=s(z')$, then $y=y'$ and $z=z'$.
--   2. Every vertex of $H$ has small neighbour mass: $d^H_{w\circ s}(y)\le e^{a}$ for every $y\in\vec E$.
--   3. Most of the triangle mass survives:
--   $$
--   (1-6D-6\delta)\,T_G(w)\le T_H(w\circ s).
--   $$
--
--   This is the abstract vertex-splitting step. Every vertex $u$ of $G$ is replaced by copies (the oriented edges leaving $u$), and the edges of $G$ are distributed among the copies. The neighbour mass of every copy is pushed down to $e^{a}$, and the relative loss of triangle mass is controlled by two quantities attached to $K$. The number $D$ measures how much the rows of $K$ change along one step of the local walk. The number $\delta$ measures how often $K$ moves an oriented edge $e$ to a copy $y$ whose reverse probability $K(y,e)$ is small compared with $w_{t(e)}e^{-a}$.
--
--   **Formalization Note** The new graph lives on the type `EdgeState G` of oriented edges, and item 1 is `EdgeProjection H G EdgeState.src`. `Stochastic K` says that every row of $K$ is a probability vector. No sign conditions are imposed on $a$, $D$ or $\delta$, and the hypothesis `Nonempty (EdgeState G)` says that $G$ has an edge.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/SplittingLoss.lean#L157-L219

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

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph OAI.CliqueFreeIndependence.WeightedGraph.Splitting
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
variable {V : Type u} [Fintype V]
attribute [local instance 10000] edgeStateDecEq
open FiniteCoupling
variable {G : SimpleGraph V}
open FiniteEntropy FiniteKernel LocalWalk

theorem OAI.CliqueFreeIndependence.WeightedGraph.Splitting.exists_graph [Nonempty (EdgeState G)] {w : V → ℝ} (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v)
    (K : Kernel (EdgeState G)) (hK : Stochastic K)
    (hblock : ∀ e z, e.src ≠ z.src → K e z = 0)
    {a D δ : ℝ}
    (hD : (∑ e, law G w e * ∑ z, transition G w e z * tv (K e) (K z)) ≤ D)
    (hδ : (∑ e, law G w e * ∑ y,
      if K y e < w e.dst * Real.exp (-a) then K e y else 0) ≤ δ) :
    ∃ H : SimpleGraph (EdgeState G), EdgeProjection H G EdgeState.src ∧
      (∀ z, neighborMass H (w ∘ EdgeState.src) z ≤ Real.exp a) ∧
      (1 - 6 * D - 6 * δ) * triangleMass G w ≤ triangleMass H (w ∘ EdgeState.src) := by sorry
