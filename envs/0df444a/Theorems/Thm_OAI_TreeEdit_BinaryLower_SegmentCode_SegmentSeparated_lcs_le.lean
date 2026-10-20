-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_SegmentCode_SegmentSeparated_lcs_le
-- name    : OAI.TreeEdit.BinaryLower.SegmentCode.SegmentSeparated.lcs_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:31:58.767692+00:00
-- url     : https://prove2.me/theorems/d439855b-8d66-4fc9-ad88-70af3017bc0e
-- title:
--   Segment separation bounds the LCS of codeword segments
-- statement:
--   A codebook assigns to each label $k\in\{0,\dots,K-1\}$ a binary block $c_k\in\{0,1\}^P$, so there are $2^{KP}$ codebooks; a uniformly random codebook has independent uniform bits. Suppose the codebook $c$ is segment separated at cutoff $a_0$. Let $k\ne l$ be labels, $a\ge a_0$, and $i,j$ with $i+a\le P$ and $j+a\le P$, and write $c_k[i,i+a)$ for the contiguous segment of $c_k$ of length $a$ starting at position $i$. Then
--   $$
--   100\,\mathrm{lcs}\bigl(c_k[i,i+a),\,c_l[j,j+a)\bigr)\le99a.
--   $$
--
--   Long segments of distinct codewords share at most $99\%$ of their length as a common subsequence.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/SegmentCodeLCS.lean#L21-L40

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.SegmentCode
open RandomMatching

theorem OAI.TreeEdit.BinaryLower.SegmentCode.SegmentSeparated.lcs_le {K P a₀ : ℕ} {c : Fin K → Fin P → Bool}
    (hc : SegmentSeparated c a₀) (k l : Fin K) (hkl : k ≠ l)
    (a i j : ℕ) (ha : a₀ ≤ a) (hi : i+a ≤ P) (hj : j+a ≤ P) :
    100 * lcs (((List.ofFn (c k)).drop i).take a)
      (((List.ofFn (c l)).drop j).take a) ≤ 99*a := by sorry
