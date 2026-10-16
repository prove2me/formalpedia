-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_LocalWalk_transition_stochastic
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.transition_stochastic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:44:15.101345+00:00
-- url     : https://prove2.me/theorems/2fbc7e90-b2ab-4356-9c73-f4ff3789e0bf
-- title:
--   The local walk on oriented edges is a stochastic kernel
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$ and let $w:V\to\mathbb{R}$ be a vertex weight with $w(u)>0$ for all $u\in V$. Write $N(u)$ for the neighbourhood of $u$ and
--
--   $$
--   W(u,v)=w\big(N(u)\cap N(v)\big)=\sum_{z\in N(u)\cap N(v)}w(z)
--   $$
--
--   for the weight of the common neighbourhood of $u$ and $v$. Let $\vec E(G)$ be the finite set of oriented edges, i.e. ordered pairs $(u,v)$ with $u\sim v$. The *local walk* is the kernel $T$ on $\vec E(G)$ defined by $T\big((u,v),(u',v')\big)=w(v')/W(u,v)$ if $u'=u$ and $v\sim v'$, and $T\big((u,v),(u',v')\big)=0$ otherwise.
--
--   Assume that $W(u,v)>0$ for every edge $uv$ of $G$. Then $T$ is a stochastic kernel: for all oriented edges $e,f\in\vec E(G)$,
--
--   $$
--   T(e,f)\ge0\qquad\text{and}\qquad\sum_{f\in\vec E(G)}T(e,f)=1 .
--   $$
--
--   From the oriented edge $(u,v)$ the walk keeps the first endpoint $u$ and moves the second endpoint to a common neighbour $v'\in N(u)\cap N(v)$, chosen with probability proportional to $w(v')$. Thus $T$ is the disjoint union, over all vertices $u$, of the $w$-weighted random walks on the induced neighbourhood graphs $G[N(u)]$. The positivity hypothesis says that every edge lies in a triangle; without it the row of an edge with $N(u)\cap N(v)=\varnothing$ would be identically zero. This Markov chain is the basic object whose smoothing and entropy are analysed in the triangle-based part of the independence-number argument.
--
--   **Formalization Note** $\vec E(G)$ is `EdgeState G`, the subtype of pairs `(u, v)` with `G.Adj u v`, whose endpoints are `e.src` and `e.dst`; $W(u,v)$ is `commonMass G w u v` and $T$ is `transition G w`. `Stochastic K` means that every row of `K` is nonnegative and sums to $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/LocalWalk.lean#L57-L75

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

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
variable {V : Type u} [Fintype V]
attribute [local instance 10000] edgeStateDecEq
open FiniteEntropy FiniteKernel
variable (G : SimpleGraph V) (w : V → ℝ)
variable {G w}

theorem OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.transition_stochastic (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v) : Stochastic (transition G w) := by sorry
