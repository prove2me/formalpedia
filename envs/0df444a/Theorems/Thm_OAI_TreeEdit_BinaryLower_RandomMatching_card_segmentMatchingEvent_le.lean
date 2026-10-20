-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_RandomMatching_card_segmentMatchingEvent_le
-- name    : OAI.TreeEdit.BinaryLower.RandomMatching.card_segmentMatchingEvent_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:23:13.032536+00:00
-- url     : https://prove2.me/theorems/666bbd10-48db-4b75-b324-c07799e113b5
-- title:
--   Counting codebooks with a prescribed long matching
-- statement:
--   A codebook assigns to each label $k\in\{0,\dots,K-1\}$ a binary block $c_k\in\{0,1\}^P$, so there are $2^{KP}$ codebooks; a uniformly random codebook has independent uniform bits. Fix distinct labels $i\ne j$, maps $u,v:\{0,\dots,a-1\}\to\{0,\dots,P-1\}$ with $v$ injective, and $s\in\mathbb N$. Let $E_s$ be the set of codebooks $c$ for which there are strictly increasing $f,g:\{0,\dots,s-1\}\to\{0,\dots,a-1\}$ with $c_i(u(f(t)))=c_j(v(g(t)))$ for all $t$. Then
--   $$
--   |E_s|\le\binom as^2\,2^{KP-s}.
--   $$
--
--   So the windows $u$ of block $i$ and $v$ of block $j$ agree along a common subsequence of length $s$ for at most a $\binom as^22^{-s}$ fraction of codebooks.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/SegmentMatchingCount.lean#L43-L73

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.RandomMatching

theorem OAI.TreeEdit.BinaryLower.RandomMatching.card_segmentMatchingEvent_le {K P a s : ℕ}
    (i j : Fin K) (hne : i ≠ j) (u v : Fin a → Fin P)
    (hv : Function.Injective v) :
    (segmentMatchingEvent s i j u v).card ≤
      (a.choose s) ^ 2 * 2 ^ (K * P - s) := by sorry
