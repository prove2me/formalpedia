-- Prove2me | Theorems.Thm_OAI_FiniteCircle_anchor_deficit_lower
-- name    : OAI.FiniteCircle.anchor_deficit_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:09:20.145713+00:00
-- url     : https://prove2.me/theorems/878d53f9-6758-46be-aac6-0d13bfdb44af
-- title:
--   Anchor-local block codes scale the LCS deficit of equal-length words by at least $\varepsilon w/2$
-- statement:
--   Let $\alpha$ be an alphabet and $w\ge1$; a block code $c:\alpha\to\{0,1\}^w$ assigns to every letter $a$ a binary codeword $c(a)=(c(a)_0,\dots,c(a)_{w-1})$, and the encoding of a word $x=x_0x_1\cdots x_{L-1}$ is the concatenation $\operatorname{enc}_c(x)=c(x_0)\,c(x_1)\cdots c(x_{L-1})\in\{0,1\}^{wL}$; positions are numbered from $0$, so position $iw+r$ with $0\le r<w$ of $\operatorname{enc}_c(x)$ is bit $r$ of the codeword of $x_i$ (the $i$-th block). For words $u,v$ let $\operatorname{lcs}(u,v)$ be the maximal length of a common subsequence and $\operatorname{def}(u,v)=|u|-\operatorname{lcs}(u,v)$ the deficit.
--
--   For a list $I=(i_1,\dots,i_m)$ of positions in $\{0,\dots,w-1\}$ write $\operatorname{span}(I)=i_m+1-i_1$ (and $0$ for the empty list). For $\varepsilon\in\mathbb{R}$, the code $c$ is called $\varepsilon$-anchor-local if the following holds for all letters $a,b\in\alpha$ (equal or not): whenever $I=(i_1<\dots<i_m)$ and $J=(j_1<\dots<j_m)$ are strictly increasing lists of positions of the same length $m\ge w/4$ that are nearly contiguous, in the sense that $\operatorname{span}(I)-m\le\varepsilon w$ and $\operatorname{span}(J)-m\le\varepsilon w$, and whose bits agree, $c(a)_{i_t}=c(b)_{j_t}$ for $t=1,\dots,m$, then $a=b$ and $i_t=j_t$ for at least one $t$.
--
--   **Theorem.** Let $w\ge1$ and $0\le\varepsilon\le\tfrac1{10}$, and let $c:\alpha\to\{0,1\}^w$ be $\varepsilon$-anchor-local. Then for all words $x,y$ over $\alpha$ with $|x|=|y|$,
--   $$
--   \frac{\varepsilon}{2}\,w\,\operatorname{def}(x,y)\ \le\ \operatorname{def}\bigl(\operatorname{enc}_c(x),\operatorname{enc}_c(y)\bigr).
--   $$
--
--   Since always $\operatorname{def}(\operatorname{enc}_c(x),\operatorname{enc}_c(y))\le w\operatorname{def}(x,y)$, the theorem says that an anchor-local code multiplies the deficit of equal-length words by a factor between $\varepsilon w/2$ and $w$. This is the lower deficit bound needed for the anchor-local binary code used in the main construction.
--
--   **Formalization Note** Anchor-locality is `AnchorLocal ε c`, the spans are `indexSpan`, and the differences $\operatorname{span}(I)-m$ are natural-number subtractions (they never truncate for strictly increasing lists). The conclusion "$i_t=j_t$ for some $t$" is `∃ i, (i, i) ∈ is.zip js`. Both deficits are natural numbers cast to $\mathbb{R}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/AnchorRecovery.lean#L254-L297

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

open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem OAI.FiniteCircle.anchor_deficit_lower {α : Type*} {w : ℕ} (hw : 0 < w) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1/10) {c : α → Fin w → Bool} (hlocal : AnchorLocal ε c)
    (x y : List α) (hlen : x.length = y.length) :
    (ε/2) * w * deficit x y ≤ (deficit (encode c x) (encode c y) : ℝ) := by sorry
