-- Prove2me | Theorems.Thm_OAI_FiniteCircle_get_encode_block
-- name    : OAI.FiniteCircle.get_encode_block
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:04:45.013009+00:00
-- url     : https://prove2.me/theorems/655164d7-de56-40a8-a03b-421658ec4696
-- title:
--   Bits of a block encoding: position $iw+r$ carries bit $r$ of the $i$-th codeword
-- statement:
--   Let $\alpha$ be an alphabet (an arbitrary type), let $w\in\mathbb{N}$, and let $c:\alpha\to\{0,1\}^w$ be a block code, assigning to every letter $a$ a binary codeword $c(a)=(c(a)_0,\dots,c(a)_{w-1})$. For a word $x=x_0x_1\cdots x_{L-1}$ over $\alpha$ (positions are numbered from $0$) its encoding is the concatenation of the codewords of its letters,
--   $$
--   \operatorname{enc}_c(x)=c(x_0)\,c(x_1)\cdots c(x_{L-1})\in\{0,1\}^{wL}.
--   $$
--
--   For every position $0\le i<L$ of $x$ and every $0\le r<w$,
--   $$
--   \operatorname{enc}_c(x)_{iw+r}=c(x_i)_r .
--   $$
--
--   That is, the encoding consists of $L$ consecutive blocks of length $w$, and the $i$-th block is the codeword of the $i$-th letter. This indexing formula is the basic tool for translating information about matched bits of two encoded words back into information about the letters of the original words; it underlies the block-by-block analysis of common subsequences of encodings.
--
--   **Formalization Note** The encoding is `encode c x = x.flatMap (fun a => List.ofFn (c a))`, with codewords given as functions `Fin w → Bool`. The statement uses `List.get` at the index `⟨i * w + r, _⟩`; the bound $iw+r<wL$ is proved inside the statement from `length_encode`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/BlockMatching.lean#L11-L31

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

theorem OAI.FiniteCircle.get_encode_block {α : Type*} {w : ℕ} (c : α → Fin w → Bool)
    (x : List α) (i : Fin x.length) (r : Fin w) :
    (encode c x).get ⟨i.val * w + r.val, by
      rw [length_encode]
      nlinarith [i.isLt, r.isLt]⟩ = c (x.get i) r := by sorry
