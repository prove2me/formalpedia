-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_common_sublist_subset_ofFn_segments
-- name    : OAI.TreeEdit.BinaryLower.common_sublist_subset_ofFn_segments
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:49:36.684022+00:00
-- url     : https://prove2.me/theorems/81e6b285-aa29-4222-bce5-fb0e652340c3
-- title:
--   Selected matched edges inside two windows give a common subsequence
-- statement:
--   Let $x\in\alpha^n$ and $y\in\alpha^m$ be words, and let $i,j$ be strictly increasing maps from $\{0,\dots,k-1\}$ to positions of $x$ and $y$ with $x_{i(t)}=y_{j(t)}$ for all $t$. Let $S\subseteq\{0,\dots,k-1\}$ be a set of indices with $a\le i(t)<a+p$ and $b\le j(t)<b+q$ for all $t\in S$. Then there is a word $z$ with
--   $$
--   z\preceq x[a,a+p),\qquad z\preceq y[b,b+q),\qquad|z|=|S|.
--   $$
--
--   Here $x[a,a+p)$ drops the first $a$ letters and keeps at most $p$, and $\preceq$ is the subsequence order; only the selected edges need to lie in the windows.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/MatchingSegments.lean#L140-L161

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

theorem OAI.TreeEdit.BinaryLower.common_sublist_subset_ofFn_segments {α : Type*} {n m k : ℕ}
    (x : Fin n → α) (y : Fin m → α)
    (i : Fin k → Fin n) (j : Fin k → Fin m)
    (hi : StrictMono i) (hj : StrictMono j)
    (hlabel : ∀ t, x (i t) = y (j t))
    (S : Finset (Fin k)) (a b p q : ℕ)
    (hi_lo : ∀ t ∈ S, a ≤ (i t : ℕ)) (hi_hi : ∀ t ∈ S, (i t : ℕ) < a + p)
    (hj_lo : ∀ t ∈ S, b ≤ (j t : ℕ)) (hj_hi : ∀ t ∈ S, (j t : ℕ) < b + q) :
    ∃ z : List α, z.Sublist (((List.ofFn x).drop a).take p) ∧
      z.Sublist (((List.ofFn y).drop b).take q) ∧ z.length = S.card := by sorry
