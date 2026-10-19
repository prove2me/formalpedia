-- Prove2me | Theorems.Thm_OAI_FiniteCircle_WordMatching_targetBlocks_card_le_three
-- name    : OAI.FiniteCircle.WordMatching.targetBlocks_card_le_three
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:06:16.970957+00:00
-- url     : https://prove2.me/theorems/f02bab8f-ad54-4e35-a59f-012c6d26793c
-- title:
--   Partners spread over at most $2w$ positions meet at most three blocks of length $w$
-- statement:
--   Let $x,y$ be words over an alphabet $\alpha$ and let $A$ be a matching of size $q$ between them: two strictly increasing maps $\lambda:\{0,\dots,q-1\}\to\{0,\dots,|x|-1\}$ and $\rho:\{0,\dots,q-1\}\to\{0,\dots,|y|-1\}$ with $x_{\lambda(k)}=y_{\rho(k)}$ for every $k$ (positions are numbered from $0$; a matching is a common subsequence of length $q$ together with its two occurrences). For a set $S\subseteq\{0,\dots,q-1\}$ of matched pairs, its right span is the set of positions of $y$ lying between two partners of elements of $S$,
--   $$
--   \operatorname{Span}_\rho(S)=\{\,j\in\{0,\dots,|y|-1\} : \rho(a)\le j\le\rho(b)\text{ for some }a,b\in S\,\},
--   $$
--   and, for $w\ge1$, its target blocks are the indices of the length-$w$ blocks of $y$ containing a partner, $T_w(S)=\{\lfloor\rho(k)/w\rfloor : k\in S\}$.
--
--   If $w\ge1$ and $|\operatorname{Span}_\rho(S)|\le 2w$, then
--   $$
--   |T_w(S)|\le 3 .
--   $$
--
--   The underlying fact is that an interval of at most $2w$ consecutive positions meets at most three of the blocks $\{tw,\dots,tw+w-1\}$, $t\in\mathbb{N}$. In the block analysis of common subsequences of encoded words, $S$ is the set of matched bits of one codeword: if their partners are not too spread out, they fall into at most three codewords of the other word, so one of these receives at least a third of them.
--
--   **Formalization Note** The right span is `A.rightSpan S`, a finite set of indices of `y`, and the target blocks are `A.targetBlocks w S = S.image (fun k => (A.right k).val / w)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/BlockMatching.lean#L120-L152

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

theorem OAI.FiniteCircle.WordMatching.targetBlocks_card_le_three (A : WordMatching x y q) {w : ℕ} (hw : 0 < w)
    {S : Finset (Fin q)} (hspan : (A.rightSpan S).card ≤ 2*w) :
    (A.targetBlocks w S).card ≤ 3 := by sorry
