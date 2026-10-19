-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Diamond_adj_old_mid
-- name    : OAI.DiamondDistortion.Diamond.adj_old_mid
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:06:41.704997+00:00
-- url     : https://prove2.me/theorems/787cc287-ff5d-443a-939e-0793d48f9e67
-- title:
--   Adjacency between old vertices and new midpoints in the countably branching diamond graph
-- statement:
--   The countably branching diamond graphs $G_0,G_1,\dots$ are built together with their edge sets $E_n$ and vertex sets $V_n$. The graph $G_0$ has the two vertices $V_0=\{0,1\}$ and one edge, $E_0=\{\ast\}$, which runs from $a_\ast=0$ to $b_\ast=1$. Given stage $n$, put
--   $$E_{n+1}=E_n\times\mathbb{N}\times\{0,1\},\qquad V_{n+1}=V_n\sqcup(E_n\times\mathbb{N}),$$
--   so that $V_{n+1}$ consists of the *old* vertices of $V_n$ together with a *midpoint* $m_{e,i}$ for every edge $e\in E_n$ and every $i\in\mathbb{N}$. If $e\in E_n$ runs from $a_e$ to $b_e$, then the edge $(e,i,0)\in E_{n+1}$ runs from $a_e$ to $m_{e,i}$ and the edge $(e,i,1)$ runs from $m_{e,i}$ to $b_e$. Two distinct vertices $u,v\in V_n$ are adjacent in $G_n$ when some edge of $E_n$ runs from $u$ to $v$ or from $v$ to $u$. Thus $G_{n+1}$ arises from $G_n$ by replacing every edge by countably many paths of length two between its endpoints, each through its own new midpoint. Each $V_n$ is regarded as a subset of $V_{n+1}$.
--
--   **Theorem.** Let $n\in\mathbb{N}$, $u\in V_n$, $e\in E_n$ and $i\in\mathbb{N}$. In $G_{n+1}$ the old vertex $u$ is adjacent to the midpoint $m_{e,i}$ if and only if $u$ is an endpoint of $e$:
--   $$u\sim_{G_{n+1}}m_{e,i}\iff u=a_e\ \text{ or }\ u=b_e .$$
--
--   This is the basic local description of one subdivision step: the new midpoint $m_{e,i}$ is joined exactly to the two endpoints of its parent edge. It is used to lift walks from $G_n$ to $G_{n+1}$ and hence to prove connectivity and the doubling of distances between old vertices.
--
--   **Formalization Note** The types are `Diamond.Edge n` and `Diamond.Vertex n`, the endpoints of an edge are `Diamond.endpoint n e false` (start) and `Diamond.endpoint n e true` (end), old vertices of stage $n+1$ are `Sum.inl u` and midpoints are `Sum.inr (e, i)`, and $G_n$ is `Diamond.graph n`, built with `SimpleGraph.fromRel`, which symmetrizes the relation and removes loops. The statement is `(graph (n+1)).Adj (Sum.inl u) (Sum.inr (e,i)) ↔ u = endpoint n e false ∨ u = endpoint n e true`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/DiamondGraph.lean#L63-L78

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

theorem OAI.DiamondDistortion.Diamond.adj_old_mid {n : ℕ} {u : Vertex n} {e : Edge n} {i : ℕ} :
    (graph (n+1)).Adj (Sum.inl u) (Sum.inr (e,i)) ↔
      u=endpoint n e false ∨ u=endpoint n e true := by sorry
