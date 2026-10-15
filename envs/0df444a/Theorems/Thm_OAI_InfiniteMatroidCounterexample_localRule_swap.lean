-- Prove2me | Theorems.Thm_OAI_InfiniteMatroidCounterexample_localRule_swap
-- name    : OAI.InfiniteMatroidCounterexample.localRule_swap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:43:30.403806+00:00
-- url     : https://prove2.me/theorems/1bda912e-0c9b-4b9a-9553-bf430bac9d5d
-- title:
--   Local basis rules are closed under single-element exchange
-- statement:
--   Let $D$ be the set of pairs $(m,g)$ with $m\in\mathbb N$ and $g:\{0,1\}^m\to\{0,1\}$, let $E_0=D\times\{0,1\}$, and let $W_m\subseteq E_0$ be the finite $m$-th block of elements $((m,g),b)$. Write $\delta_m(X)=|X\cap W_m|/|W_m|$, call $X$ *small* if $\delta_m(X)\to0$, and say that $X$ is in the *class* of $T$ if $X\triangle T$ is small. Let $P_n=W_0\cup\dots\cup W_{n-1}$. For $T,X\subseteq E_0$ and $n\in\mathbb N$ the *probe* is
--   $$\phi^T_n(X)=\bigl(|X\cap P_n|-|T\cap P_n|\bigr)+|P_n|\Bigl(\sup_{m\ge n}d^T_m(X)+\inf_{m\ge n}d^T_m(X)\Bigr),\qquad d^T_m(X)=\delta_m(X)-\delta_m(T),$$
--   and $\underline\phi^{\,T}(X)=\liminf_{n\to\infty}\phi^T_n(X)\in[-\infty,+\infty]$. The two *local rules* of $T$ are
--   $$\mathcal L_0(T)=\bigl\{X:\ X\triangle T\text{ small},\ -1<\underline\phi^{\,T}(X)\le0\bigr\},\qquad \mathcal L_1(T)=\bigl\{X:\ E_0\setminus X\in\mathcal L_0(E_0\setminus T)\bigr\}.$$
--
--   **Theorem.** Let $T\subseteq E_0$, $s\in\{0,1\}$ and $B\in\mathcal L_s(T)$. For every $e\in B$ and every $f\in E_0\setminus B$,
--   $$(B\setminus\{e\})\cup\{f\}\in\mathcal L_s(T).$$
--
--   Closure under single exchanges is one of the axioms of a basis system; it is inherited by the union of the local rules over a family of prototypes and yields the base-exchange axiom of the self-dual matroid on $E_0$.
--
--   **Formalization Note** `LocalRule s T` is `LocalUpper T` if `s = true` and `LocalLower T` if `s = false`, with `LocalUpper T = {X | Xᶜ ∈ LocalLower Tᶜ}`; the exchanged set is written `insert f (B \ {e})`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/BasisExtension.lean#L143-L157

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
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DensityIdeal
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Reservations
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BasisExtension

open OAI OAI.InfiniteMatroidCounterexample
open Set Filter
open scoped Topology symmDiff

theorem OAI.InfiniteMatroidCounterexample.localRule_swap {s : Bool} {T B : Set E0} (hB : B ∈ LocalRule s T)
    (e : E0) (he : e ∈ B) (f : E0) (hf : f ∉ B) : insert f (B \ {e}) ∈ LocalRule s T := by sorry
