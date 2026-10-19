-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Diamond_dist_old
-- name    : OAI.DiamondDistortion.Diamond.dist_old
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:09:16.601061+00:00
-- url     : https://prove2.me/theorems/951d8eb5-41fe-40c6-9223-f8e391b0de7d
-- title:
--   One subdivision step doubles graph distances between old vertices of the diamond graph
-- statement:
--   The countably branching diamond graphs $G_0,G_1,\dots$ are built together with their edge sets $E_n$ and vertex sets $V_n$. The graph $G_0$ has the two vertices $V_0=\{0,1\}$ and one edge, $E_0=\{\ast\}$, which runs from $a_\ast=0$ to $b_\ast=1$. Given stage $n$, put
--   $$E_{n+1}=E_n\times\mathbb{N}\times\{0,1\},\qquad V_{n+1}=V_n\sqcup(E_n\times\mathbb{N}),$$
--   so that $V_{n+1}$ consists of the *old* vertices of $V_n$ together with a *midpoint* $m_{e,i}$ for every edge $e\in E_n$ and every $i\in\mathbb{N}$. If $e\in E_n$ runs from $a_e$ to $b_e$, then the edge $(e,i,0)\in E_{n+1}$ runs from $a_e$ to $m_{e,i}$ and the edge $(e,i,1)$ runs from $m_{e,i}$ to $b_e$. Two distinct vertices $u,v\in V_n$ are adjacent in $G_n$ when some edge of $E_n$ runs from $u$ to $v$ or from $v$ to $u$. Thus $G_{n+1}$ arises from $G_n$ by replacing every edge by countably many paths of length two between its endpoints, each through its own new midpoint. Each $V_n$ is regarded as a subset of $V_{n+1}$, and $d_{G_n}(u,v)$ denotes the shortest-path distance (number of edges) in $G_n$.
--
--   **Theorem.** For every $n\in\mathbb{N}$ and all $u,v\in V_n$,
--   $$d_{G_{n+1}}(u,v)=2\,d_{G_n}(u,v).$$
--
--   Consequently the normalized distances $d_n(u,v)=d_{G_n}(u,v)/2^n$, in which every edge of $G_n$ has length $2^{-n}$, are compatible across stages: $d_{n+1}(u,v)=d_n(u,v)$ for old vertices. This is what allows a map on $G_{n+1}$ to be restricted to the old vertices and compared with stage $n$ in inductive distortion arguments.
--
--   **Formalization Note** The types are `Diamond.Edge n` and `Diamond.Vertex n`, the endpoints of an edge are `Diamond.endpoint n e false` (start) and `Diamond.endpoint n e true` (end), old vertices of stage $n+1$ are `Sum.inl u` and midpoints are `Sum.inr (e, i)`, and $G_n$ is `Diamond.graph n`, built with `SimpleGraph.fromRel`, which symmetrizes the relation and removes loops. The distance is Mathlib's `SimpleGraph.dist`, a natural number; it is the length of a shortest walk here because all stages are connected.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/DiamondGraph.lean#L177-L190

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

theorem OAI.DiamondDistortion.Diamond.dist_old (n : ℕ) (u v : Vertex n) :
    (graph (n+1)).dist (Sum.inl u) (Sum.inl v)=2*(graph n).dist u v := by sorry
