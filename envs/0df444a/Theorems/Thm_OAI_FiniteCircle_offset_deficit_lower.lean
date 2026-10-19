-- Prove2me | Theorems.Thm_OAI_FiniteCircle_offset_deficit_lower
-- name    : OAI.FiniteCircle.offset_deficit_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:12:31.011065+00:00
-- url     : https://prove2.me/theorems/b5ce1e8a-4b31-4371-8282-c9e723e8e3fb
-- title:
--   Offset-local block codes scale the LCS deficit of equal-length words by at least $\frac{\eta}{4+32\eta}\,w$
-- statement:
--   Let $\alpha$ be an alphabet and $w\in\mathbb{N}$; a block code $c:\alpha\to\{0,1\}^w$ assigns to every letter $a$ a binary codeword $c(a)=(c(a)_0,\dots,c(a)_{w-1})$, and the encoding of a word $x=x_0x_1\cdots x_{L-1}$ is the concatenation $\operatorname{enc}_c(x)=c(x_0)\,c(x_1)\cdots c(x_{L-1})\in\{0,1\}^{wL}$; positions are numbered from $0$, so position $iw+r$ with $0\le r<w$ of $\operatorname{enc}_c(x)$ is bit $r$ of the codeword of $x_i$ (the $i$-th block). For words $X,Y$ let $\operatorname{lcs}(X,Y)$ be the maximal length of a common subsequence and $\operatorname{def}(X,Y)=|X|-\operatorname{lcs}(X,Y)$ the deficit. Put $m=\lfloor w/8\rfloor$ and, for a letter $a$ and an offset $s$ with $s+m\le w$, let $c(a)[s,s+m)=c(a)_s\cdots c(a)_{s+m-1}$ be the window of length $m$ of its codeword. For $\delta\in\mathbb{R}$ the code $c$ is $\delta$-offset-local if
--   $$
--   \operatorname{lcs}\bigl(c(a)[s,s+m),\,c(b)[t,t+m)\bigr)\le(1-\delta)\,m
--   $$
--   for all letters $a\ne b$ and all offsets $s,t$ with $s+m\le w$ and $t+m\le w$.
--
--   **Theorem.** Let $w\ge12$ and let $\delta,\eta\in\mathbb{R}$ satisfy $\delta\le1$, $0\le\eta\le1$ and $2\eta w<\delta\lfloor w/8\rfloor$. If $c$ is $\delta$-offset-local, then for all words $x,y$ over $\alpha$ with $|x|=|y|$,
--   $$
--   \frac{\eta}{4+32\eta}\,w\,\operatorname{def}(x,y)\ \le\ \operatorname{def}\bigl(\operatorname{enc}_c(x),\operatorname{enc}_c(y)\bigr).
--   $$
--
--   Since always $\operatorname{def}(\operatorname{enc}_c(x),\operatorname{enc}_c(y))\le w\operatorname{def}(x,y)$, an offset-local code multiplies the deficit of equal-length words by a factor between $\frac{\eta}{4+32\eta}w$ and $w$. This supplies the lower deficit bound needed for the offset-local binary code used in the main construction.
--
--   **Formalization Note** Offset-locality is `OffsetLocal δ c`, whose windows are `interval c a s (w/8)` with the natural-number quotient `w/8`. Both deficits are natural numbers cast to $\mathbb{R}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/OffsetRecovery.lean#L374-L439

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion
import Definitions.Def_OAI_Combinatorics_FiniteCircle_BlockMatching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_OffsetRecovery

open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem OAI.FiniteCircle.offset_deficit_lower {α : Type*} {w : ℕ} (hw : 12 ≤ w) {δ η : ℝ}
    (hδ : δ ≤ 1) (hη0 : 0 ≤ η) (hη : η ≤ 1)
    (hfit : 2*η*w < δ*(w/8 : ℕ)) {c : α → Fin w → Bool} (hc : OffsetLocal δ c)
    (x y : List α) (hlen : x.length=y.length) :
    (η/(4+32*η))*w*deficit x y ≤ (deficit (encode c x) (encode c y) : ℝ) := by sorry
