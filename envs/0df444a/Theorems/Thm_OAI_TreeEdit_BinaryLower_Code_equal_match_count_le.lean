-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_Code_equal_match_count_le
-- name    : OAI.TreeEdit.BinaryLower.Code.equal_match_count_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:33:21.477155+00:00
-- url     : https://prove2.me/theorems/c88e051c-fa97-4c16-8ff2-03d66b0f2e87
-- title:
--   Counting matched positions by residues modulo the block width
-- statement:
--   Let $P>0$ and let $f,g:\{0,\dots,N-1\}\to\mathbb N$ be strictly increasing. Suppose every set $S$ of indices on which both $i\mapsto\lfloor f(i)/P\rfloor$ and $i\mapsto\lfloor g(i)/P\rfloor$ are strictly increasing has $|S|\le L$. Then
--   $$
--   N\le P\,L.
--   $$
--
--   In the application, $f$ and $g$ list the bit positions of an increasing matching between two encodings, and their quotients by $P$ are block indices; a set on which both block maps increase is a matching of the source words, so $L$ can be their longest common subsequence length. This replaces an edge-colouring argument by a colouring by residues.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/CodeEqualMatches.lean#L12-L35

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Code

theorem OAI.TreeEdit.BinaryLower.Code.equal_match_count_le {N P L : ℕ} (hP : 0 < P)
    (f g : Fin N → ℕ) (hf : StrictMono f) (hg : StrictMono g)
    (hL : ∀ s : Finset (Fin N),
      StrictMonoOn (fun i => f i / P) (s : Set (Fin N)) →
      StrictMonoOn (fun i => g i / P) (s : Set (Fin N)) → s.card ≤ L) :
    N ≤ P * L := by sorry
