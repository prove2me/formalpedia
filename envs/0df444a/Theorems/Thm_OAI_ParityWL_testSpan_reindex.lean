-- Prove2me | Theorems.Thm_OAI_ParityWL_testSpan_reindex
-- name    : OAI.ParityWL.testSpan_reindex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:48:41.581978+00:00
-- url     : https://prove2.me/theorems/e7947d35-d7d7-4769-8ef8-9cb24324e294
-- title:
--   Test spans are closed under reindexing of tuple coordinates
-- statement:
--   Let $G$ and $H$ be graphs on finite vertex sets $V$ and $W$, and write $[k]=\{0,\dots,k-1\}$. A *rooted test* with $k$ roots and width $t$ is a finite set $P$ carrying a symmetric relation $R$ (loops allowed), a root map $\varrho\colon[k]\to P$ (not necessarily injective), and a rooted tree decomposition of $(P,R)$ (every element of $P$ lies in some bag, the bags containing a given element form a connected subtree, and every related pair lies in a common bag) whose bags have at most $t$ elements, in which every non-root bag shares fewer than $t$ elements with its parent bag, and whose root bag is exactly $\varrho([k])$. For $x\in V^k$, the count $\mathrm{cnt}_P(G,x)\in\mathbb{Q}$ is the number of maps $f\colon P\to V$ with $f(p)f(p')\in E(G)$ whenever $R(p,p')$ and $f(\varrho(i))=x_i$ for all $i\in[k]$; similarly $\mathrm{cnt}_P(H,y)$ for $y\in W^k$.
--
--   On the disjoint union $\mathcal{X}_k=V^k\sqcup W^k$ of the $k$-tuples of both graphs, the *evaluation* of a test $P$ is the function $\mathrm{ev}_P\colon\mathcal{X}_k\to\mathbb{Q}$ equal to $\mathrm{cnt}_P(G,\cdot)$ on $V^k$ and to $\mathrm{cnt}_P(H,\cdot)$ on $W^k$. The *test span* $\mathcal{T}_{k,t}$ is the $\mathbb{Q}$-linear span, inside the space of all functions $\mathcal{X}_k\to\mathbb{Q}$, of the evaluations $\mathrm{ev}_P$ of all rooted tests $P$ with $k$ roots and width $t$.
--
--   For a map $\varphi\colon[k]\to[m]$ and a function $f\colon\mathcal{X}_k\to\mathbb{Q}$, the *reindexed* function $\varphi^{\ast}f\colon\mathcal{X}_m\to\mathbb{Q}$ is $(\varphi^{\ast}f)(x)=f(x\circ\varphi)$, where $x\circ\varphi=(x_{\varphi(0)},\dots,x_{\varphi(k-1)})$ for $x$ in $V^m$ or in $W^m$.
--
--   **Theorem.** Let $k,m,t\in\mathbb{N}$ with $m\le t$, and let $\varphi\colon[k]\to[m]$ be any map. Then
--   $$
--   f\in\mathcal{T}_{k,t}\quad\Longrightarrow\quad\varphi^{\ast}f\in\mathcal{T}_{m,t}.
--   $$
--
--   Reindexing covers forgetting, repeating and permuting coordinates. It lets functions of $k$-tuples built from tests be regarded as functions of $m$-tuples, and it is one of the closure operations used to show that the indicator functions of Weisfeiler–Leman colour classes lie in the span of rooted-test counts.
--
--   **Formalization Note** Tuple pairs are `TuplePair V W k`, the sum type of `Fin k → V` and `Fin k → W`; the span is `testSpan G H k t`, a `Submodule` over the rationals spanned by `testEval G H P` for `P : RootedTest k t`. The reindexing map is the linear map `reindexLinear φ`, precomposition with `x ↦ x ∘ φ` on both summands.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/TestAlgebra.lean#L184-L203

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

theorem OAI.ParityWL.testSpan_reindex {k m t : ℕ} (hm : m ≤ t) (φ : Fin k → Fin m)
    {f : TuplePair V W k → ℚ} (hf : f ∈ testSpan G H k t) :
    reindexLinear φ f ∈ testSpan G H m t := by sorry
