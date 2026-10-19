-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Diamond_connected
-- name    : OAI.DiamondDistortion.Diamond.connected
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:07:26.410449+00:00
-- url     : https://prove2.me/theorems/2a6292d3-f385-4a33-9445-071f1af2d9b3
-- title:
--   Every stage of the countably branching diamond graph is connected
-- statement:
--   The countably branching diamond graphs $G_0,G_1,\dots$ are built together with their edge sets $E_n$ and vertex sets $V_n$. The graph $G_0$ has the two vertices $V_0=\{0,1\}$ and one edge, $E_0=\{\ast\}$, which runs from $a_\ast=0$ to $b_\ast=1$. Given stage $n$, put
--   $$E_{n+1}=E_n\times\mathbb{N}\times\{0,1\},\qquad V_{n+1}=V_n\sqcup(E_n\times\mathbb{N}),$$
--   so that $V_{n+1}$ consists of the *old* vertices of $V_n$ together with a *midpoint* $m_{e,i}$ for every edge $e\in E_n$ and every $i\in\mathbb{N}$. If $e\in E_n$ runs from $a_e$ to $b_e$, then the edge $(e,i,0)\in E_{n+1}$ runs from $a_e$ to $m_{e,i}$ and the edge $(e,i,1)$ runs from $m_{e,i}$ to $b_e$. Two distinct vertices $u,v\in V_n$ are adjacent in $G_n$ when some edge of $E_n$ runs from $u$ to $v$ or from $v$ to $u$. Thus $G_{n+1}$ arises from $G_n$ by replacing every edge by countably many paths of length two between its endpoints, each through its own new midpoint. Each $V_n$ is regarded as a subset of $V_{n+1}$.
--
--   **Theorem.** For every $n\in\mathbb{N}$ the graph $G_n$ is connected: $V_n$ is nonempty and for all $u,v\in V_n$ there is a walk
--   $$u=w_0\sim w_1\sim\cdots\sim w_\ell=v\qquad\text{in }G_n .$$
--
--   Connectivity ensures that the shortest-path distance $d_{G_n}$ is a genuine metric on all of $V_n$; it is needed before distances in the diamond graphs can be computed or compared between stages.
--
--   **Formalization Note** The types are `Diamond.Edge n` and `Diamond.Vertex n`, the endpoints of an edge are `Diamond.endpoint n e false` (start) and `Diamond.endpoint n e true` (end), old vertices of stage $n+1$ are `Sum.inl u` and midpoints are `Sum.inr (e, i)`, and $G_n$ is `Diamond.graph n`, built with `SimpleGraph.fromRel`, which symmetrizes the relation and removes loops. Connectivity is Mathlib's `SimpleGraph.Connected` (nonempty and preconnected).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/DiamondGraph.lean#L111-L135

import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality
import Definitions.Def_OAI_Analysis_DiamondDistortion_ForestModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_DiamondGraph

open OAI OAI.DiamondDistortion OAI.DiamondDistortion.Diamond
universe u v
open scoped BigOperators Classical Topology
open Set

theorem OAI.DiamondDistortion.Diamond.connected (n : ℕ) : (graph n).Connected := by sorry
