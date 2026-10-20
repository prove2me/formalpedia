-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_Code_encoded_block_segment_separation
-- name    : OAI.TreeEdit.BinaryLower.Code.encoded_block_segment_separation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:52:20.397469+00:00
-- url     : https://prove2.me/theorems/5f2dd6fc-bc74-4f96-9b7f-ac23cf3b2cc3
-- title:
--   Codeword separation gives block-segment separation of encodings
-- statement:
--   Let $c$ assign to each letter a codeword of length $P$, and write $w[i,i+a)$ for the contiguous segment of $w$ of length $a$ starting at position $i$. Suppose distinct codewords are separated at cutoff $a_0$: for letters $k\ne l$, all $a\ge a_0$ and all $i,j$ with $i+a\le P$ and $j+a\le P$,
--   $$
--   100\,\mathrm{lcs}\bigl(c(k)[i,i+a),\,c(l)[j,j+a)\bigr)\le99a.
--   $$
--
--   Then for source words $x,y$ of length $M$, the encodings $c(x),c(y)$ (concatenated codewords) are block-segment separated at cutoff $a_0$ for the block pairs $(b_1,b_2)$ with $x_{b_1}\ne y_{b_2}$: for $a\ge a_0$, every common subsequence $w$ of a length-$a$ window inside block $b_1$ of $c(x)$ and a length-$a$ window inside block $b_2$ of $c(y)$ satisfies $100|w|\le99a$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/EncodedSegmentSeparation.lean#L11-L46

import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteCoordinates
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteWordDetection
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CheapTranslations
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Distortion
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ParameterImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteParameters
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EncodedImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFamilyTransfer
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeNumerics
import Definitions.Def_OAI_Combinatorics_BinaryEdit_RandomMatching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_SegmentMatchingCount
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeUnionBound
import Definitions.Def_OAI_Combinatorics_BinaryEdit_SegmentCode
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeAdditive
import Definitions.Def_OAI_Combinatorics_BinaryEdit_MatchingSpanBudget
import Definitions.Def_OAI_Combinatorics_BinaryEdit_MatchingSegments
import Definitions.Def_OAI_Combinatorics_BinaryEdit_UnequalSegments

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Code
universe u v

theorem OAI.TreeEdit.BinaryLower.Code.encoded_block_segment_separation {α : Type u} {β : Type v}
    {M P a₀ : ℕ} (c : α → Word β P)
    (hsep : ∀ k l : α, k ≠ l → ∀ a i j : ℕ, a₀ ≤ a →
      i + a ≤ P → j + a ≤ P →
      100 * lcs (((c k).val.drop i).take a) (((c l).val.drop j).take a) ≤ 99 * a)
    (x y : List α) (hx : x.length = M) (hy : y.length = M) :
    BlockSegmentSeparation (encodedBit c x hx) (encodedBit c y hy)
      (fun b => x[b.1]? ≠ y[b.2]?) a₀ := by sorry
