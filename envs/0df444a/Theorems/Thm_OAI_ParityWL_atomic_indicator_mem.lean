-- Prove2me | Theorems.Thm_OAI_ParityWL_atomic_indicator_mem
-- name    : OAI.ParityWL.atomic_indicator_mem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T05:02:09.038185+00:00
-- url     : https://prove2.me/theorems/f9e074d9-d0a2-4679-9093-9bd7402edf5c
-- title:
--   Indicators of atomic types lie in the span of rooted-test counts
-- statement:
--   Let $G$ and $H$ be graphs on finite vertex sets $V$ and $W$, and write $[k]=\{0,\dots,k-1\}$. A *rooted test* with $k$ roots and width $t$ is a finite set $P$ carrying a symmetric relation $R$ (loops allowed), a root map $\varrho\colon[k]\to P$ (not necessarily injective), and a rooted tree decomposition of $(P,R)$ (every element of $P$ lies in some bag, the bags containing a given element form a connected subtree, and every related pair lies in a common bag) whose bags have at most $t$ elements, in which every non-root bag shares fewer than $t$ elements with its parent bag, and whose root bag is exactly $\varrho([k])$. For $x\in V^k$, the count $\mathrm{cnt}_P(G,x)\in\mathbb{Q}$ is the number of maps $f\colon P\to V$ with $f(p)f(p')\in E(G)$ whenever $R(p,p')$ and $f(\varrho(i))=x_i$ for all $i\in[k]$; similarly $\mathrm{cnt}_P(H,y)$ for $y\in W^k$.
--
--   On the disjoint union $\mathcal{X}_k=V^k\sqcup W^k$ of the $k$-tuples of both graphs, the *evaluation* of a test $P$ is the function $\mathrm{ev}_P\colon\mathcal{X}_k\to\mathbb{Q}$ equal to $\mathrm{cnt}_P(G,\cdot)$ on $V^k$ and to $\mathrm{cnt}_P(H,\cdot)$ on $W^k$. The *test span* $\mathcal{T}_{k,t}$ is the $\mathbb{Q}$-linear span, inside the space of all functions $\mathcal{X}_k\to\mathbb{Q}$, of the evaluations $\mathrm{ev}_P$ of all rooted tests $P$ with $k$ roots and width $t$.
--
--   The *atomic type* of a tuple $x\in V^k$ is the $k\times k$ array $\mathrm{atp}(x)=\big([x_i=x_j],\,[x_ix_j\in E(G)]\big)_{i,j\in[k]}$ of pairs of truth values, and similarly for $y\in W^k$ with $H$ in place of $G$; this defines a map $\mathrm{atp}$ from $\mathcal{X}_k$ to the finite set of $k\times k$ arrays of pairs of truth values.
--
--   **Theorem.** Let $k,t\in\mathbb{N}$ with $k\le t$. For every $k\times k$ array $d$ of pairs of truth values,
--   $$
--   \mathbf 1_{\mathrm{atp}=d}\in\mathcal{T}_{k,t},\qquad \mathbf 1_{\mathrm{atp}=d}(x)=\begin{cases}1,&\mathrm{atp}(x)=d,\\0,&\text{otherwise.}\end{cases}
--   $$
--
--   This is the base case of the expressibility of Weisfeiler–Leman colours by rooted-test counts: the round-$0$ colour classes of $k$-tuples, in both graphs simultaneously, are linear combinations of homomorphism-count functions of rooted tests of width $t$.
--
--   **Formalization Note** Tuple pairs are `TuplePair V W k`, the sum type of `Fin k → V` and `Fin k → W`; the span is `testSpan G H k t`, a `Submodule` over the rationals spanned by `testEval G H P` for `P : RootedTest k t`. The atomic type is `pairAtomic G H`, with values in `AtomicType k`, the type of functions `Fin k → Fin k → Bool × Bool`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/ColorSpan.lean#L39-L56

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
import Definitions.Def_OAI_Combinatorics_ParityLifts_ColorSpan

open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical
variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

theorem OAI.ParityWL.atomic_indicator_mem {k t : ℕ} (hkt : k ≤ t) (d : AtomicType k) :
    (fun x => if pairAtomic G H x = d then (1 : ℚ) else 0) ∈ testSpan G H k t := by sorry
