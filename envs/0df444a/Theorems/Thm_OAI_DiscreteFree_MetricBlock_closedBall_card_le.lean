-- Prove2me | Theorems.Thm_OAI_DiscreteFree_MetricBlock_closedBall_card_le
-- name    : OAI.DiscreteFree.MetricBlock.closedBall_card_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:51:45.519688+00:00
-- url     : https://prove2.me/theorems/f368a59b-9464-43f5-bb0a-9a0da37c4d81
-- title:
--   Closed balls of radius below the attachment radius in a metric block are no larger than the set of short port words
-- statement:
--   Let $G$ be a port graph on a vertex set $X$ with port set $D$: an involution $e\mapsto\bar e$ of $D$ and a move map $X\times D\to X$, $(x,e)\mapsto x\cdot e$, such that $(x\cdot e)\cdot\bar e=x$ for all $x\in X$ and $e\in D$. A word $w=e_1e_2\cdots e_k$ of ports (an arbitrary finite list, not necessarily reduced) moves $x$ along a walk to $x\cdot w=(\cdots((x\cdot e_1)\cdot e_2)\cdots)\cdot e_k$, and $|w|=k$ is its length. Assume $D$ is finite. Let $\chi\colon X\to C$ be a coloring with values in a finite set $C$, and let $\mathrm{cap}$ and $R\ge1$ be natural numbers. For $x\in X$ let $\ell(x)=(\ell_i(x))_{i\in C}\in\{0,\dots,\mathrm{cap}\}^{C}$ be its capped label vector, where $\ell_i(x)$ is the length of a shortest walk from $x$ to a vertex of color $i$, truncated at $\mathrm{cap}$. The points of the metric block are the vertices and the anchors,
--   $$
--   \mathcal{M}=X\sqcup\mathcal{A},\qquad \mathcal{A}=\{\ell(x):x\in X\} .
--   $$
--
--   For distinct points the weight is
--   $$
--   \omega(x,y)=\begin{cases}1 & y=x\cdot e\ \text{for some port } e,\\ 4R+\mathrm{cap} & \text{otherwise,}\end{cases}\qquad
--   \omega(x,a)=\omega(a,x)=\begin{cases}R & a=\ell(x),\\ 4R+\mathrm{cap} & \text{otherwise,}\end{cases}\qquad
--   \omega(a,b)=2R+\max_{i\in C}|a_i-b_i|
--   $$
--   for vertices $x,y$ and anchors $a,b$, and the metric $d$ of the block is the shortest-path metric: $d(u,v)$ is the minimum of $\sum_{t=1}^{k}\omega(z_{t-1},z_t)$ over finite chains $u=z_0,z_1,\dots,z_k=v$ $(k\ge1)$, and $d(u,u)=0$.
--
--   **Theorem.** Let $n\in\mathbb{N}$ with $n<R$. Then for every point $u\in\mathcal{M}$,
--   $$
--   \#\{\,v\in\mathcal{M}:\ d(v,u)\le n\,\}\ \le\ \#\{\,w\in D^{*}:\ |w|\le n\,\},
--   $$
--   the number of port words of length at most $n$.
--
--   Below the attachment radius the block looks exactly like the port graph, so its closed balls have uniformly bounded size, independent of the graph and of the coloring. In the block obstruction it bounds the number of points of a finite support set that lie within a fixed distance $n<R$ of a given point, which controls the number of admissible transitions in the counting argument.
--
--   **Formalization Note** The hypotheses `[Fintype D]`, `[Fintype C]` and `[Fact (0 < R)]` are present (the last one is needed for the metric instance on `Point G color cap R`), and `hn : n < R`. The left side is `Nat.card` of `Metric.closedBall u n`; this ball is in fact finite (it injects into a finite set), so the bound concerns its genuine number of elements. The right side is `Fintype.card (BoundedWords D n)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/Attachment.lean#L145-L157

import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment

open OAI OAI.DiscreteFree OAI.DiscreteFree.MetricBlock
open scoped BigOperators ENNReal
open scoped Classical
variable {X D C : Type*} [Fintype C] (G : PortGraph X D) (color : X → C) (cap R : ℕ)
variable [Fintype D]
variable [Fact (0 < R)]

theorem OAI.DiscreteFree.MetricBlock.closedBall_card_le (n : ℕ) (hn : n < R) (u : Point G color cap R) :
    Nat.card (Metric.closedBall u (n : ℝ)) ≤ Fintype.card (BoundedWords D n) := by sorry
