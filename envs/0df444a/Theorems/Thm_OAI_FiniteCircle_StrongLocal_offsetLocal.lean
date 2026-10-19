-- Prove2me | Theorems.Thm_OAI_FiniteCircle_StrongLocal_offsetLocal
-- name    : OAI.FiniteCircle.StrongLocal.offsetLocal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:16:54.96899+00:00
-- url     : https://prove2.me/theorems/fd50d4d9-3c56-482a-82e4-da5fb3ade050
-- title:
--   Strongly local binary codes are offset-local with $\delta=2^{-20}$
-- statement:
--   Let $\alpha$ be any set of letters, $w$ a natural number and $c:\alpha\to\{0,1\}^{w}$ a binary code; $c(a)_i$ denotes the bit of the codeword $c(a)$ at position $i\in[w]=\{0,\dots,w-1\}$. For a strictly increasing list of positions $I=(i_1<\dots<i_L)$ in $[w]$ let $\operatorname{span}(I)=i_L-i_1+1$ (and $0$ for the empty list). The code is *strongly local* if for all letters $a,b$ and all strictly increasing lists $I=(i_1<\dots<i_L)$, $J=(j_1<\dots<j_L)$ in $[w]$ of the same length $L$ with $w\le16L$, $\operatorname{span}(I)-L\le w/2^{20}$, $\operatorname{span}(J)-L\le w/2^{20}$ and $c(a)_{i_r}=c(b)_{j_r}$ for all $r$, one has $a=b$ and $i_r=j_r$ for some $r$.
--
--   For a letter $a$ and natural numbers $s,u$ with $s+u\le w$ write $c(a)[s,s+u)$ for the word of $u$ consecutive bits $c(a)_s,\dots,c(a)_{s+u-1}$, and let $\operatorname{lcs}(x,y)$ be the length of a longest common subsequence of two words. The code is *offset-local with parameter* $\delta$ if for all letters $a\ne b$ and all offsets $s,t$ with $s+\lfloor w/8\rfloor\le w$ and $t+\lfloor w/8\rfloor\le w$, the windows $c(a)[s,s+\lfloor w/8\rfloor)$ and $c(b)[t,t+\lfloor w/8\rfloor)$ have LCS length at most $(1-\delta)\lfloor w/8\rfloor$.
--
--   **Theorem.** If $c$ is strongly local, $w>0$ and $8\mid w$, then $c$ is offset-local with parameter $\delta=2^{-20}$: for all letters $a\ne b$ and all offsets $s,t$ with $s+w/8\le w$ and $t+w/8\le w$,
--
--   $$
--   \operatorname{lcs}\Bigl(c(a)\bigl[s,s+\tfrac w8\bigr),\ c(b)\bigl[t,t+\tfrac w8\bigr)\Bigr)\ \le\ \Bigl(1-\frac{1}{2^{20}}\Bigr)\frac{w}{8}.
--   $$
--
--   Offset-locality says that windows of length $w/8$ cut from the codewords of two different letters, at arbitrary and possibly different offsets, are far apart in the longest-common-subsequence sense. It is one of the two code properties (with anchor-locality) required by the main theorem on $\ell^1$ embeddings of edit distance, where it is used to show that encoding words letter by letter preserves the deficit up to constant factors. This lemma shows that a single strongly local code, whose existence is established by a counting argument, has this property.
--
--   **Formalization Note** The window is `interval c a s (w/8)`, i.e. `((List.ofFn (c a)).drop s).take (w/8)`; the definition of offset-locality uses natural division $w/8$, which is exact under the hypothesis $8\mid w$. The parameter appears as `1/1048576`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Codes.lean#L47-L121

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
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Codes

open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem OAI.FiniteCircle.StrongLocal.offsetLocal {α : Type*} {w : ℕ} {c : α → Fin w → Bool}
    (hc : StrongLocal c) (hw : 0 < w) (hd : 8 ∣ w) : OffsetLocal (1/1048576) c := by sorry
