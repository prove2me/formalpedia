-- Prove2me | Theorems.Thm_OAI_FiniteCircle_exists_strongLocal
-- name    : OAI.FiniteCircle.exists_strongLocal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:15:29.869506+00:00
-- url     : https://prove2.me/theorems/0d59c5e7-14d2-4420-8aac-89a98a037b22
-- title:
--   Existence of strongly local binary codes of width $O(\log|\alpha|)$
-- statement:
--   Let $\alpha$ be a finite alphabet with $|\alpha|\ge2$. A *binary code of width* $w$ is a map $c:\alpha\to\{0,1\}^{w}$; write $c(a)_i$ for the bit of the codeword $c(a)$ at position $i\in[w]=\{0,1,\dots,w-1\}$. For a strictly increasing list of positions $I=(i_1<i_2<\dots<i_L)$ in $[w]$ with $L\ge1$ put $\operatorname{span}(I)=i_L-i_1+1$, so that $\operatorname{span}(I)-L$ is the number of positions between $i_1$ and $i_L$ that $I$ skips (the empty list has span $0$).
--
--   The code $c$ is called *strongly local* if the following holds for all letters $a,b\in\alpha$ and all strictly increasing lists $I=(i_1<\dots<i_L)$ and $J=(j_1<\dots<j_L)$ in $[w]$ of the same length $L$: if
--
--   1. $w\le16L$,
--   2. $\operatorname{span}(I)-L\le w/2^{20}$ and $\operatorname{span}(J)-L\le w/2^{20}$, and
--   3. $c(a)_{i_r}=c(b)_{j_r}$ for every $r=1,\dots,L$,
--
--   then $a=b$ and $i_r=j_r$ for at least one index $r$. In words: every long (at least $w/16$ pairs), nearly gap-free, order-preserving matching of positions along which the codewords $c(a)$ and $c(b)$ agree must join a codeword with itself, and must match some position with itself.
--
--   **Theorem.** For every finite alphabet $\alpha$ with $|\alpha|\ge2$ there exist a width $w\in\mathbb{N}$ and a strongly local code $c:\alpha\to\{0,1\}^{w}$ such that
--
--   $$
--   2^{26}\le w,\qquad 64\mid w,\qquad w\le 67108928\,\log\bigl(2|\alpha|\bigr),
--   $$
--
--   where $\log$ is the natural logarithm and $67108928=2^{26}+64$.
--
--   Thus binary codes that are rigid against long, nearly gap-free matchings of agreeing bits exist with width only logarithmic in the alphabet size. In the edit-distance embedding argument this single code is used for both codes required by the "two codes" condition of the main theorem: strong locality implies anchor-locality with parameter $2^{-20}$ and, since $8\mid w$, offset-locality with parameter $2^{-20}$, while the width bound is the logarithmic width condition with constant $67108928$.
--
--   **Formalization Note** Codes are functions `α → Fin w → Bool`, position lists are pairwise strictly increasing lists in `Fin w`, and the number of skipped positions is `indexSpan is - is.length` (natural subtraction, which does not truncate for increasing lists), compared with the real number $w/1048576$. The conclusion "$i_r=j_r$ for some $r$" is phrased as some pair $(i,i)$ occurring in `is.zip js`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/RandomCodes.lean#L192-L241

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
import Definitions.Def_OAI_Combinatorics_FiniteCircle_RandomCodes

open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem OAI.FiniteCircle.exists_strongLocal (α : Type*) [Fintype α] (hA : 2 ≤ Fintype.card α) :
    ∃ (w : ℕ) (c : α → Fin w → Bool), 67108864 ≤ w ∧ 64 ∣ w ∧
      (w : ℝ) ≤ 67108928 * Real.log (2*Fintype.card α) ∧ StrongLocal c := by sorry
