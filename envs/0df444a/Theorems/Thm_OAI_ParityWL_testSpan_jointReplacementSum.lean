-- Prove2me | Theorems.Thm_OAI_ParityWL_testSpan_jointReplacementSum
-- name    : OAI.ParityWL.testSpan_jointReplacementSum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:58:46.370917+00:00
-- url     : https://prove2.me/theorems/a26e0ede-98d2-4798-8897-c46fafe90d35
-- title:
--   Test spans are closed under joint replacement sums when $k+1\le t$
-- statement:
--   Let $G$ and $H$ be graphs on finite vertex sets $V$ and $W$, and write $[k]=\{0,\dots,k-1\}$. A *rooted test* with $k$ roots and width $t$ is a finite set $P$ carrying a symmetric relation $R$ (loops allowed), a root map $\varrho\colon[k]\to P$ (not necessarily injective), and a rooted tree decomposition of $(P,R)$ (every element of $P$ lies in some bag, the bags containing a given element form a connected subtree, and every related pair lies in a common bag) whose bags have at most $t$ elements, in which every non-root bag shares fewer than $t$ elements with its parent bag, and whose root bag is exactly $\varrho([k])$. For $x\in V^k$, the count $\mathrm{cnt}_P(G,x)\in\mathbb{Q}$ is the number of maps $f\colon P\to V$ with $f(p)f(p')\in E(G)$ whenever $R(p,p')$ and $f(\varrho(i))=x_i$ for all $i\in[k]$; similarly $\mathrm{cnt}_P(H,y)$ for $y\in W^k$.
--
--   On the disjoint union $\mathcal{X}_k=V^k\sqcup W^k$ of the $k$-tuples of both graphs, the *evaluation* of a test $P$ is the function $\mathrm{ev}_P\colon\mathcal{X}_k\to\mathbb{Q}$ equal to $\mathrm{cnt}_P(G,\cdot)$ on $V^k$ and to $\mathrm{cnt}_P(H,\cdot)$ on $W^k$. The *test span* $\mathcal{T}_{k,t}$ is the $\mathbb{Q}$-linear span, inside the space of all functions $\mathcal{X}_k\to\mathbb{Q}$, of the evaluations $\mathrm{ev}_P$ of all rooted tests $P$ with $k$ roots and width $t$.
--
--   For a tuple $x$ write $x[i\leftarrow v]$ for $x$ with its $i$-th entry replaced by $v$. For a family $f=(f_i)_{i\in[k]}$ of functions $\mathcal{X}_k\to\mathbb{Q}$, the *joint replacement sum* $Jf\colon\mathcal{X}_k\to\mathbb{Q}$ is
--   $$
--   (Jf)(x)=\sum_{v\in V}\ \prod_{i\in[k]}f_i(x[i\leftarrow v])\quad(x\in V^k),\qquad(Jf)(x)=\sum_{v\in W}\ \prod_{i\in[k]}f_i(x[i\leftarrow v])\quad(x\in W^k).
--   $$
--
--   **Theorem.** Let $k,t\in\mathbb{N}$ with $k+1\le t$, and let $f_0,\dots,f_{k-1}\in\mathcal{T}_{k,t}$. Then
--   $$
--   Jf\in\mathcal{T}_{k,t}.
--   $$
--
--   The joint replacement sum is the linear shadow of one refinement step of the joint Weisfeiler–Leman convention, where a single new vertex $v$ is substituted into all coordinates at once and the resulting vector of colours is recorded. Its closure property is used to show that the indicator functions of joint Weisfeiler–Leman colour classes lie in the test span; the extra room $k+1\le t$ accommodates the additional vertex.
--
--   **Formalization Note** Tuple pairs are `TuplePair V W k`, the sum type of `Fin k → V` and `Fin k → W`; the span is `testSpan G H k t`, a `Submodule` over the rationals spanned by `testEval G H P` for `P : RootedTest k t`. The joint replacement sum is `jointReplacementSum f` for `f : Fin k → TuplePair V W k → ℚ`, given by the displayed formula.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/Interpolation.lean#L116-L152

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
import Definitions.Def_OAI_Combinatorics_ParityLifts_Interpolation

open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical
variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

theorem OAI.ParityWL.testSpan_jointReplacementSum {k t : ℕ} (hkt : k + 1 ≤ t)
    {f : Fin k → TuplePair V W k → ℚ} (hf : ∀ i, f i ∈ testSpan G H k t) :
    jointReplacementSum f ∈ testSpan G H k t := by sorry
