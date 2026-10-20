-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_common_sublist_in_segments
-- name    : OAI.TreeEdit.BinaryLower.common_sublist_in_segments
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:48:21.114064+00:00
-- url     : https://prove2.me/theorems/9a8c5bef-0f47-456d-976d-d340ad64519a
-- title:
--   A matching inside two windows is a common subsequence of the segments
-- statement:
--   Let $x,y$ be words and let $i,j$ be strictly increasing maps from $\{0,\dots,k-1\}$ to positions of $x$ and $y$ with $x_{i(t)}=y_{j(t)}$ for all $t$. Suppose $a\le i(t)<a+p$ and $b\le j(t)<b+q$ for all $t$. Write $x[a,a+p)$ for the segment obtained by dropping the first $a$ letters of $x$ and keeping at most $p$ letters, and similarly $y[b,b+q)$. Then there is a word $z$ with
--   $$
--   z\preceq x[a,a+p),\qquad z\preceq y[b,b+q),\qquad|z|=k,
--   $$
--   where $z\preceq w$ means that $z$ is a (not necessarily contiguous) subsequence of $w$.
--
--   An increasing matching confined to two windows thus yields a common subsequence of the corresponding contiguous segments of the same length.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/MatchingSegments.lean#L89-L119

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower

theorem OAI.TreeEdit.BinaryLower.common_sublist_in_segments {α : Type*} (x y : List α) {k : ℕ}
    (i : Fin k → Fin x.length) (j : Fin k → Fin y.length)
    (hi : StrictMono i) (hj : StrictMono j)
    (hlabel : ∀ t, x.get (i t) = y.get (j t))
    (a b p q : ℕ)
    (hi_lo : ∀ t, a ≤ (i t : ℕ)) (hi_hi : ∀ t, (i t : ℕ) < a + p)
    (hj_lo : ∀ t, b ≤ (j t : ℕ)) (hj_hi : ∀ t, (j t : ℕ) < b + q) :
    ∃ z : List α, z.Sublist ((x.drop a).take p) ∧
      z.Sublist ((y.drop b).take q) ∧ z.length = k := by sorry
