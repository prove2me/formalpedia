-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_SegmentCode_comparisonBad_fraction_le
-- name    : OAI.TreeEdit.BinaryLower.SegmentCode.comparisonBad_fraction_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:28:05.498053+00:00
-- url     : https://prove2.me/theorems/9b153c15-9de1-4467-a8a0-62a9f8e054b8
-- title:
--   A single segment comparison is rarely bad
-- statement:
--   A codebook assigns to each label $k\in\{0,\dots,K-1\}$ a binary block $c_k\in\{0,1\}^P$, so there are $2^{KP}$ codebooks; a uniformly random codebook has independent uniform bits. A comparison is a tuple $t=(k,l,a,i,j)$ with labels $k,l<K$ and $a,i,j\in\{0,\dots,P\}$. Given a cutoff $a_0$, its bad set $B_{a_0}(t)$ is empty unless $k\ne l$, $a\ge a_0$, $i+a\le P$ and $j+a\le P$; in that case it consists of the codebooks for which the length-$a$ window of $c_k$ starting at $i$ and the length-$a$ window of $c_l$ starting at $j$ share a common subsequence of length $a-\lfloor a/100\rfloor$. Then
--   $$
--   \frac{|B_{a_0}(t)|}{2^{KP}}\le\left(\frac9{10}\right)^{a_0}.
--   $$
--
--   A uniformly random codebook therefore makes any one long comparison bad with probability exponentially small in the cutoff.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/SegmentCode.lean#L47-L75

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

theorem OAI.TreeEdit.BinaryLower.SegmentCode.comparisonBad_fraction_le {K P : ℕ} (a₀ : ℕ)
    (t : SegmentComparison K (P+1)) :
    ((comparisonBad a₀ t).card : ℝ) / Fintype.card (Fin K → Fin P → Bool) ≤
      (9/10 : ℝ)^a₀ := by sorry
