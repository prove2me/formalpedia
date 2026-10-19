-- Prove2me | Theorems.Thm_OAI_FiniteCircle_WordMatching_offset_interior_labels
-- name    : OAI.FiniteCircle.WordMatching.offset_interior_labels
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:10:03.16305+00:00
-- url     : https://prove2.me/theorems/cb428640-bd53-4d9b-a872-12e3800b47cb
-- title:
--   Offset-local codes: a matched interior bit of a nearly intact block is matched into the same letter
-- statement:
--   Let $\alpha$ be an alphabet and $w\ge1$; a block code $c:\alpha\to\{0,1\}^w$ assigns to every letter $a$ a binary codeword $c(a)=(c(a)_0,\dots,c(a)_{w-1})$, and the encoding of a word $x=x_0x_1\cdots x_{L-1}$ is the concatenation $\operatorname{enc}_c(x)=c(x_0)\,c(x_1)\cdots c(x_{L-1})\in\{0,1\}^{wL}$; positions are numbered from $0$, so position $iw+r$ with $0\le r<w$ of $\operatorname{enc}_c(x)$ is bit $r$ of the codeword of $x_i$ (the $i$-th block). Let $\operatorname{lcs}$ denote the length of a longest common subsequence. Put $u=\lfloor w/8\rfloor$ and, for a letter $a$ and an offset $s$ with $s+u\le w$, let $c(a)[s,s+u)=c(a)_s\,c(a)_{s+1}\cdots c(a)_{s+u-1}$ be the window of length $u$ of its codeword. For $\delta\in\mathbb{R}$, the code is $\delta$-offset-local if for all distinct letters $a\neq b$ and all offsets $s,t$ with $s+u\le w$ and $t+u\le w$,
--   $$
--   \operatorname{lcs}\bigl(c(a)[s,s+u),\,c(b)[t,t+u)\bigr)\le(1-\delta)\,u .
--   $$
--
--   Let $x,y$ be words over $\alpha$ and let $A$ be a matching of size $q$ between $\operatorname{enc}_c(x)$ and $\operatorname{enc}_c(y)$: strictly increasing maps $\lambda,\rho$ from $\{0,\dots,q-1\}$ to the positions of $\operatorname{enc}_c(x)$, respectively $\operatorname{enc}_c(y)$, such that the bits at $\lambda(k)$ and $\rho(k)$ are equal for every $k$. For a block index $i$ let $B_i=\{k:\lfloor\lambda(k)/w\rfloor=i\}$, let $U_i=w-|B_i|$ be its source loss and $V_i=|\operatorname{Span}_\rho(B_i)|-|B_i|$ its span loss, where $\operatorname{Span}_\rho(B_i)=\{j:\rho(a)\le j\le\rho(b)\text{ for some }a,b\in B_i\}$.
--
--   **Theorem.** Let $w\ge1$ and $\delta\le1$, and let $c$ be $\delta$-offset-local. Let $k<q$, and let $i<|x|$ and $j<|y|$ be the blocks of its endpoints, $\lfloor\lambda(k)/w\rfloor=i$ and $\lfloor\rho(k)/w\rfloor=j$. Assume that the offset $p=\lambda(k)\bmod w$ is interior, $u\le p$ and $p+u\le w$, and that block $i$ is nearly intact:
--   $$
--   U_i+V_i<\delta\,u .
--   $$
--   Then $x_i=y_j$.
--
--   In words: when block $i$ of $\operatorname{enc}_c(x)$ is matched almost completely and its partners are almost contiguous, every matched bit at an interior offset of the block is matched into the codeword of the same letter. This is the label-recovery step in the lower bound for deficits of encodings by offset-local codes.
--
--   **Formalization Note** Offset-locality is `OffsetLocal δ c`, the windows are `interval c a s (w/8)`, and $u$ is the natural-number quotient `w/8`. The losses are `A.sourceLoss w i` and `A.spanLoss w i` (natural numbers; their sum is cast to $\mathbb{R}$). The blocks are given as `i : Fin x.length` and `j : Fin y.length`, and the conclusion is `x.get i = y.get j`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/WindowMatching.lean#L150-L254

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

open OAI OAI.FiniteCircle OAI.FiniteCircle.WordMatching
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
variable {α : Type*} {x y : List α} {w q : ℕ} {c : α → Fin w → Bool}

theorem OAI.FiniteCircle.WordMatching.offset_interior_labels (hw : 0 < w) {δ : ℝ} (hδ : δ ≤ 1)
    (hc : OffsetLocal δ c) (A : WordMatching (encode c x) (encode c y) q)
    (k : Fin q) (i : Fin x.length) (j : Fin y.length)
    (hi : (A.left k).val/w=i.val) (hj : (A.right k).val/w=j.val)
    (hp : w/8 ≤ (A.left k).val%w) (hp' : (A.left k).val%w+w/8 ≤ w)
    (hloss : (A.sourceLoss w i+A.spanLoss w i : ℕ)  <  δ*(w/8 : ℕ)) :
    x.get i=y.get j := by sorry
