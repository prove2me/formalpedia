-- Prove2me | Theorems.Thm_OAI_FiniteCircle_WordMatching_block_before_card_le
-- name    : OAI.FiniteCircle.WordMatching.block_before_card_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:07:00.826789+00:00
-- url     : https://prove2.me/theorems/6180c16d-5c4e-4b06-b5e8-1d742ccfe887
-- title:
--   Matched pairs of a block lying before a given pair are at most its offset in the block
-- statement:
--   Let $x,y$ be words over an alphabet $\alpha$ and let $A$ be a matching of size $q$ between them: two strictly increasing maps $\lambda:\{0,\dots,q-1\}\to\{0,\dots,|x|-1\}$ and $\rho:\{0,\dots,q-1\}\to\{0,\dots,|y|-1\}$ with $x_{\lambda(k)}=y_{\rho(k)}$ for every $k$ (positions are numbered from $0$; a matching is a common subsequence of length $q$ together with its two occurrences). For $w,i\in\mathbb{N}$ let $B_i=\{k:\lfloor\lambda(k)/w\rfloor=i\}$ be the set of matched pairs whose left position lies in the $i$-th block of length $w$ of $x$.
--
--   For every $k\in B_i$,
--   $$
--   \#\{\,l\in B_i : l<k\,\}\ \le\ \lambda(k)\bmod w .
--   $$
--
--   In words: the matched pairs of block $i$ preceding $k$ have their left positions at pairwise distinct offsets inside the block, all strictly smaller than the offset $\lambda(k)\bmod w$ of $k$, so there are at most that many of them. Together with the mirror statement (at most $w-1-(\lambda(k)\bmod w)$ matched pairs of the block follow $k$), this counts the matched pairs of a block on either side of a given pair; it is used to show that two anchor pairs of different blocks cannot land in the same block of the other word, and to bound duplicated offsets in consecutive blocks.
--
--   **Formalization Note** No hypothesis $w>0$ is needed: with Lean's conventions $n/0=0$ and $n \bmod 0=n$, for $w=0$ the block $B_0$ is the whole index set, every other block is empty, and the statement says that at most $\lambda(k)$ pairs precede $k$, which is also true. The block $B_i$ is `A.sourceBlock w i`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/AnchorRecovery.lean#L127-L140

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

theorem OAI.FiniteCircle.WordMatching.block_before_card_le (A : WordMatching x y q) {w i : ℕ}
    {k : Fin q} (hk : k ∈ A.sourceBlock w i) :
    ((A.sourceBlock w i).filter (fun l => l < k)).card ≤ (A.left k).val%w := by sorry
