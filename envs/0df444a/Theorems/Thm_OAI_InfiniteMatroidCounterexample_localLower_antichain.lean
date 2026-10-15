-- Prove2me | Theorems.Thm_OAI_InfiniteMatroidCounterexample_localLower_antichain
-- name    : OAI.InfiniteMatroidCounterexample.localLower_antichain
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:41:56.467987+00:00
-- url     : https://prove2.me/theorems/9ab833fa-9727-404f-a1fa-ebe45f015e70
-- title:
--   Lower local bases of a density class form an antichain
-- statement:
--   Let $D$ be the set of pairs $(m,g)$ with $m\in\mathbb N$ and $g:\{0,1\}^m\to\{0,1\}$, let $E_0=D\times\{0,1\}$, and let $W_m\subseteq E_0$ be the finite $m$-th block of elements $((m,g),b)$. Write $\delta_m(X)=|X\cap W_m|/|W_m|$, call $X$ *small* if $\delta_m(X)\to0$, and say that $X$ is in the *class* of $T$ if $X\triangle T$ is small. Let $P_n=W_0\cup\dots\cup W_{n-1}$. For $T,X\subseteq E_0$ and $n\in\mathbb N$ the *probe* is
--   $$\phi^T_n(X)=\bigl(|X\cap P_n|-|T\cap P_n|\bigr)+|P_n|\Bigl(\sup_{m\ge n}d^T_m(X)+\inf_{m\ge n}d^T_m(X)\Bigr),\qquad d^T_m(X)=\delta_m(X)-\delta_m(T),$$
--   and $\underline\phi^{\,T}(X)=\liminf_{n\to\infty}\phi^T_n(X)\in[-\infty,+\infty]$. The *lower local rule* of $T$ is
--   $$\mathcal L_0(T)=\bigl\{X\subseteq E_0:\ X\triangle T \text{ is small and } -1<\underline\phi^{\,T}(X)\le 0\bigr\}.$$
--
--   **Theorem.** For every $T\subseteq E_0$, the family $\mathcal L_0(T)$ is an antichain under inclusion: if $X,Y\in\mathcal L_0(T)$ and $X\subseteq Y$, then $X=Y$.
--
--   The families $\mathcal L_0(T)$ and their complementary counterparts are the local pieces of the basis family of the self-dual matroid on $E_0$. Bases of a matroid must form an antichain, and this lemma supplies that property for the lower rule (the upper rule follows by complementation).
--
--   **Formalization Note** `LocalLower T` is `{X | SameClass T X ∧ LowerBasis (fProbe T) X}`, where `LowerBasis f X` means `-1 < probeLiminf f X ∧ probeLiminf f X ≤ 0` and `probeLiminf` is the lower limit taken in `EReal`. The tail supremum and infimum are `sSup`/`sInf` of the bounded nonempty sets of values $d^T_m(X)\in[-1,1]$, $m\ge n$, so they are the usual ones.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/LocalBases.lean#L100-L120

import Mathlib
import Definitions.Def_InfiniteMatroid
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cardinality
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Ideals
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_OrdinalRank
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_FiniteCounting
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Basic
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BlockDensity
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Columns
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cesaro
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_ProbeLimits
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_SparsePerturbation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Interpolation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_LocalBases

open OAI OAI.InfiniteMatroidCounterexample
open Set Filter
open scoped Topology symmDiff

theorem OAI.InfiniteMatroidCounterexample.localLower_antichain (T : Set E0) :
    ∀ ⦃X Y⦄, X ∈ LocalLower T → Y ∈ LocalLower T → X ⊆ Y → X = Y := by sorry
