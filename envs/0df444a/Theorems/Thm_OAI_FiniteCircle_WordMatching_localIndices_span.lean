-- Prove2me | Theorems.Thm_OAI_FiniteCircle_WordMatching_localIndices_span
-- name    : OAI.FiniteCircle.WordMatching.localIndices_span
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:05:35.377136+00:00
-- url     : https://prove2.me/theorems/68bc19d5-7b6b-4ebb-87c8-95f9852ed744
-- title:
--   Within one block, the offset span of matched positions equals their positional span
-- statement:
--   Let $x,y$ be words over an alphabet $\alpha$ and let $A$ be a matching of size $q$ between them: two strictly increasing maps $\lambda:\{0,\dots,q-1\}\to\{0,\dots,|x|-1\}$ and $\rho:\{0,\dots,q-1\}\to\{0,\dots,|y|-1\}$ with $x_{\lambda(k)}=y_{\rho(k)}$ for every $k$ (positions are numbered from $0$; a matching is a common subsequence of length $q$ together with its two occurrences). Fix a block length $w\ge1$ and a block index $i\in\mathbb{N}$, and let
--   $$
--   B_i=\{\,k : \lfloor \lambda(k)/w\rfloor=i\,\}
--   $$
--   be the set of matched pairs whose left position lies in the $i$-th block $\{iw,\dots,iw+w-1\}$ of $x$.
--
--   For a list $(a_1,\dots,a_m)$ of numbers in $\{0,\dots,w-1\}$ define its index span as $\operatorname{span}(a_1,\dots,a_m)=a_m+1-a_1$ if $m\ge1$, and $\operatorname{span}()=0$ for the empty list. Let $S\subseteq B_i$, let $k_1<\dots<k_m$ be the elements of $S$ in increasing order, and form the list of local offsets $\bigl(\lambda(k_1)\bmod w,\dots,\lambda(k_m)\bmod w\bigr)$. Then
--   $$
--   \operatorname{span}\bigl(\lambda(k_1)\bmod w,\ \dots,\ \lambda(k_m)\bmod w\bigr)=\#\bigl\{\,j\in\{0,\dots,|x|-1\} : \lambda(a)\le j\le\lambda(b)\text{ for some }a,b\in S\,\bigr\}.
--   $$
--   The right-hand side counts the positions of $x$ between the first and the last left endpoint of $S$, so it equals $\lambda(k_m)-\lambda(k_1)+1$ when $S\neq\emptyset$; when $S=\emptyset$ both sides are $0$.
--
--   The identity turns a statement about offsets inside a single codeword (how spread out a set of matched offsets is) into a count of positions of the word $x$, which can then be compared with the number of unmatched positions of the block. It is used when an anchor-type local property of a block code is applied to the part of a common subsequence that lies in one block.
--
--   **Formalization Note** The offset list is `A.localIndices hw S`, a list in `Fin w` built from `S.orderEmbOfFin`, and the index span is `indexSpan` (defined with natural-number subtraction). The right-hand side is `(A.symm.rightSpan S).card`, the right span of $S$ for the reversed matching, i.e. a set of positions of $x$. The hypothesis `hw : 0 < w` is needed to form the offsets as elements of `Fin w`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/BlockMatching.lean#L88-L105

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
variable {α : Type*} {x y : List α} {q : ℕ}

theorem OAI.FiniteCircle.WordMatching.localIndices_span (A : WordMatching x y q) {w i : ℕ} (hw : 0 < w)
    {S : Finset (Fin q)} (hS : S ⊆ A.sourceBlock w i) :
    indexSpan (A.localIndices hw S) = (A.symm.rightSpan S).card := by sorry
