-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_RandomMatching_segmentMatchingEvent_fraction_le
-- name    : OAI.TreeEdit.BinaryLower.RandomMatching.segmentMatchingEvent_fraction_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:24:03.509673+00:00
-- url     : https://prove2.me/theorems/46ae7203-6c10-432d-b980-d7fd34f64423
-- title:
--   Probability that two windows share a long matching
-- statement:
--   A codebook assigns to each label $k\in\{0,\dots,K-1\}$ a binary block $c_k\in\{0,1\}^P$, so there are $2^{KP}$ codebooks; a uniformly random codebook has independent uniform bits. Fix distinct labels $i\ne j$, maps $u,v:\{0,\dots,a-1\}\to\{0,\dots,P-1\}$ with $v$ injective, and $s\le a$. Let $E_s$ be the set of codebooks for which some strictly increasing $f,g:\{0,\dots,s-1\}\to\{0,\dots,a-1\}$ satisfy $c_i(u(f(t)))=c_j(v(g(t)))$ for all $t$. Then
--   $$
--   \frac{|E_s|}{2^{KP}}\le\frac{\binom as^2}{2^s}.
--   $$
--
--   This is the previous count in probabilistic form: for a uniformly random codebook the two windows share a common subsequence of length $s$ with probability at most $\binom as^22^{-s}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/SegmentMatchingCount.lean#L75-L91

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

theorem OAI.TreeEdit.BinaryLower.RandomMatching.segmentMatchingEvent_fraction_le {K P a s : ℕ}
    (i j : Fin K) (hne : i ≠ j) (u v : Fin a → Fin P)
    (hv : Function.Injective v) (hs : s ≤ a) :
    ((segmentMatchingEvent s i j u v).card : ℝ) / (2 : ℝ) ^ (K * P) ≤
      ((a.choose s : ℝ) ^ 2) / (2 : ℝ) ^ s := by sorry
