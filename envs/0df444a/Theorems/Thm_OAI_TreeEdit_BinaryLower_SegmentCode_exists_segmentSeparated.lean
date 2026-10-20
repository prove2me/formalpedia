-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_SegmentCode_exists_segmentSeparated
-- name    : OAI.TreeEdit.BinaryLower.SegmentCode.exists_segmentSeparated
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:31:14.128+00:00
-- url     : https://prove2.me/theorems/0fb9e417-a72c-466a-982a-2e4d1694dc00
-- title:
--   Existence of a segment-separated binary codebook
-- statement:
--   A codebook assigns to each label $k\in\{0,\dots,K-1\}$ a binary block $c_k\in\{0,1\}^P$, so there are $2^{KP}$ codebooks; a uniformly random codebook has independent uniform bits. Let $K,P,a_0\in\mathbb N$ satisfy
--   $$
--   K^2(P+1)^3\left(\frac9{10}\right)^{a_0}<1.
--   $$
--
--   Then some codebook is segment separated at cutoff $a_0$: for all labels $k\ne l$, all $a\ge a_0$ and all $i,j$ with $i+a\le P$ and $j+a\le P$, every common subsequence of the length-$a$ windows of $c_k$ at $i$ and of $c_l$ at $j$, given by strictly increasing position maps of length $s$, has $100s\le99a$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/SegmentCode.lean#L77-L103

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
open RandomMatching CodeUnionBound

theorem OAI.TreeEdit.BinaryLower.SegmentCode.exists_segmentSeparated (K P a₀ : ℕ)
    (hprob : (K : ℝ)^2 * ((P+1 : ℕ) : ℝ)^3 * (9/10 : ℝ)^a₀ < 1) :
    ∃ c : Fin K → Fin P → Bool, SegmentSeparated c a₀ := by sorry
