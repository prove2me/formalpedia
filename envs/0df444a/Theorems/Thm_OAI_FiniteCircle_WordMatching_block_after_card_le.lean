-- Prove2me | Theorems.Thm_OAI_FiniteCircle_WordMatching_block_after_card_le
-- name    : OAI.FiniteCircle.WordMatching.block_after_card_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:07:45.236128+00:00
-- url     : https://prove2.me/theorems/44d52f73-1439-42f8-9656-76306740f4c3
-- title:
--   Matched pairs of a block lying after a given pair are at most $w-1$ minus its offset
-- statement:
--   Let $x,y$ be words over an alphabet $\alpha$ and let $A$ be a matching of size $q$ between them: two strictly increasing maps $\lambda:\{0,\dots,q-1\}\to\{0,\dots,|x|-1\}$ and $\rho:\{0,\dots,q-1\}\to\{0,\dots,|y|-1\}$ with $x_{\lambda(k)}=y_{\rho(k)}$ for every $k$ (positions are numbered from $0$; a matching is a common subsequence of length $q$ together with its two occurrences). For $w\ge1$ and $i\in\mathbb{N}$ let $B_i=\{k:\lfloor\lambda(k)/w\rfloor=i\}$ be the set of matched pairs whose left position lies in the $i$-th block $\{iw,\dots,iw+w-1\}$ of $x$.
--
--   If $w\ge1$, then for every $k\in B_i$,
--   $$
--   \#\{\,l\in B_i : k<l\,\}\ \le\ w-(\lambda(k)\bmod w)-1 .
--   $$
--
--   In words: the matched pairs of block $i$ following $k$ have their left positions at pairwise distinct offsets in $\{(\lambda(k)\bmod w)+1,\dots,w-1\}$, so there are at most $w-1-(\lambda(k)\bmod w)$ of them. Together with the mirror statement for the pairs preceding $k$, this counts the matched pairs of a block on either side of a given pair; it is used in the anchor and duplicate-offset arguments for encoded words.
--
--   **Formalization Note** The right-hand side uses natural-number subtraction, but since $\lambda(k)\bmod w<w$ for $w\ge1$ no truncation occurs. The block $B_i$ is `A.sourceBlock w i`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/AnchorRecovery.lean#L142-L155

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

theorem OAI.FiniteCircle.WordMatching.block_after_card_le (A : WordMatching x y q) {w i : ℕ} (hw : 0 < w)
    {k : Fin q} (hk : k ∈ A.sourceBlock w i) :
    ((A.sourceBlock w i).filter (fun l => k < l)).card ≤ w - (A.left k).val%w - 1 := by sorry
