-- Prove2me | Theorems.Thm_OAI_ParityWL_testSpan_sumInsert
-- name    : OAI.ParityWL.testSpan_sumInsert
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:50:53.827291+00:00
-- url     : https://prove2.me/theorems/930a0218-932c-46af-9890-8f62d49a11ec
-- title:
--   Summing out an inserted coordinate maps $\mathcal{T}_{k+1,t}$ into $\mathcal{T}_{k,t}$ when $k<t$
-- statement:
--   Let $G$ and $H$ be graphs on finite vertex sets $V$ and $W$, and write $[k]=\{0,\dots,k-1\}$. A *rooted test* with $k$ roots and width $t$ is a finite set $P$ carrying a symmetric relation $R$ (loops allowed), a root map $\varrho\colon[k]\to P$ (not necessarily injective), and a rooted tree decomposition of $(P,R)$ (every element of $P$ lies in some bag, the bags containing a given element form a connected subtree, and every related pair lies in a common bag) whose bags have at most $t$ elements, in which every non-root bag shares fewer than $t$ elements with its parent bag, and whose root bag is exactly $\varrho([k])$. For $x\in V^k$, the count $\mathrm{cnt}_P(G,x)\in\mathbb{Q}$ is the number of maps $f\colon P\to V$ with $f(p)f(p')\in E(G)$ whenever $R(p,p')$ and $f(\varrho(i))=x_i$ for all $i\in[k]$; similarly $\mathrm{cnt}_P(H,y)$ for $y\in W^k$.
--
--   On the disjoint union $\mathcal{X}_k=V^k\sqcup W^k$ of the $k$-tuples of both graphs, the *evaluation* of a test $P$ is the function $\mathrm{ev}_P\colon\mathcal{X}_k\to\mathbb{Q}$ equal to $\mathrm{cnt}_P(G,\cdot)$ on $V^k$ and to $\mathrm{cnt}_P(H,\cdot)$ on $W^k$. The *test span* $\mathcal{T}_{k,t}$ is the $\mathbb{Q}$-linear span, inside the space of all functions $\mathcal{X}_k\to\mathbb{Q}$, of the evaluations $\mathrm{ev}_P$ of all rooted tests $P$ with $k$ roots and width $t$.
--
--   For $i\in[k+1]$ and a $k$-tuple $x$, let $\mathrm{ins}_i(y,x)=(x_0,\dots,x_{i-1},y,x_i,\dots,x_{k-1})$ be the $(k+1)$-tuple obtained by inserting $y$ at position $i$. For $f\colon\mathcal{X}_{k+1}\to\mathbb{Q}$, the *insertion sum* $\sigma_i f\colon\mathcal{X}_k\to\mathbb{Q}$ is
--   $$
--   (\sigma_i f)(x)=\sum_{y\in V}f(\mathrm{ins}_i(y,x))\quad(x\in V^k),\qquad(\sigma_i f)(x)=\sum_{y\in W}f(\mathrm{ins}_i(y,x))\quad(x\in W^k).
--   $$
--
--   **Theorem.** Let $k,t\in\mathbb{N}$ with $k<t$ and let $i\in[k+1]$. Then
--   $$
--   f\in\mathcal{T}_{k+1,t}\quad\Longrightarrow\quad\sigma_i f\in\mathcal{T}_{k,t}.
--   $$
--
--   Summing over the possible values of one coordinate is the algebraic counterpart of the quantifier step in Weisfeiler–Leman refinement; together with reindexing, this closure property shows that the replacement-sum operators modelling refinement preserve the test span.
--
--   **Formalization Note** Tuple pairs are `TuplePair V W k`, the sum type of `Fin k → V` and `Fin k → W`; the span is `testSpan G H k t`, a `Submodule` over the rationals spanned by `testEval G H P` for `P : RootedTest k t`. The insertion sum is the linear map `sumInsertLinear i`, defined with `Fin.insertNth`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/TestAlgebra.lean#L217-L231

import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BagTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_TagSizes
import Definitions.Def_OAI_Combinatorics_ParityLifts_Detection
import Definitions.Def_OAI_Combinatorics_ParityLifts_RankedTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_RootedTests
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueVertices
import Definitions.Def_OAI_Combinatorics_ParityLifts_Rerooting
import Definitions.Def_OAI_Combinatorics_ParityLifts_TestAlgebra

open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical
variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

theorem OAI.ParityWL.testSpan_sumInsert {k t : ℕ} (hk : k < t) (i : Fin (k + 1))
    {f : TuplePair V W (k + 1) → ℚ} (hf : f ∈ testSpan G H (k + 1) t) :
    sumInsertLinear i f ∈ testSpan G H k t := by sorry
