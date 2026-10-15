-- Prove2me | Theorems.Thm_OAI_DiscreteFree_MetricBlock_short_finite
-- name    : OAI.DiscreteFree.MetricBlock.short_finite
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:50:52.340534+00:00
-- url     : https://prove2.me/theorems/8a0311a2-6f79-4586-b83e-4174e6f14e80
-- title:
--   Each point of a metric block is short-related to only finitely many points
-- statement:
--   Let $G$ be a port graph on a vertex set $X$ with port set $D$: an involution $e\mapsto\bar e$ of $D$ and a move map $X\times D\to X$, $(x,e)\mapsto x\cdot e$, such that $(x\cdot e)\cdot\bar e=x$ for all $x\in X$ and $e\in D$. A word $w=e_1e_2\cdots e_k$ of ports (an arbitrary finite list, not necessarily reduced) moves $x$ along a walk to $x\cdot w=(\cdots((x\cdot e_1)\cdot e_2)\cdots)\cdot e_k$, and $|w|=k$ is its length. Let $\chi\colon X\to C$ be a coloring and let $\mathrm{cap}\in\mathbb{N}$. For $x\in X$ let $\ell(x)=(\ell_i(x))_{i\in C}\in\{0,\dots,\mathrm{cap}\}^{C}$ be its capped label vector, where $\ell_i(x)$ is the length of a shortest walk from $x$ to a vertex of color $i$, truncated at $\mathrm{cap}$. The points of the metric block are the vertices and the anchors,
--   $$
--   \mathcal{M}=X\sqcup\mathcal{A},\qquad \mathcal{A}=\{\ell(x):x\in X\} .
--   $$
--
--   For $n\in\mathbb{N}$ the short relation $u\sim_n v$ on $\mathcal{M}$ is defined as follows: for vertices, $x\sim_n y$ if $y=x\cdot w$ for some port word $w$ with $|w|\le n$; for anchors, $a\sim_n b$ if $a=b$; a vertex and an anchor are never related.
--
--   **Theorem.** Assume the port set $D$ is finite. Then for every $n\in\mathbb{N}$ and every point $u\in\mathcal{M}$ the set
--   $$
--   \{\,v\in\mathcal{M}:\ u\sim_n v\,\}
--   $$
--   is finite.
--
--   The block also carries a shortest-path metric depending on a radius parameter $R\ge1$, in which each graph edge has length $1$ while every other step between distinct points costs at least $R$; consequently, for $n<R$ the closed ball of radius $n$ about $u$ is contained in the set above. This lemma therefore makes small balls of the block finite, and it is the finiteness input for the counting bound on such balls.
--
--   **Formalization Note** The relation is `ShortRelation G color cap R n u v` on `Point G color cap R`, the sum type of `X` and the anchor subtype of label vectors. The parameter `R` enters only the metric, which plays no role here, and no finiteness of the color type `C` is assumed (the instance is omitted); only the port type `D` is finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/Attachment.lean#L93-L106

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

omit [Fintype C] in
theorem OAI.DiscreteFree.MetricBlock.short_finite (n : ℕ) (u : Point G color cap R) :
    {v | ShortRelation G color cap R n u v}.Finite := by sorry
