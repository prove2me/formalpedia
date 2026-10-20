-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_Code_equal_label_match_count_le
-- name    : OAI.TreeEdit.BinaryLower.Code.equal_label_match_count_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:34:27.977289+00:00
-- url     : https://prove2.me/theorems/f614e22f-1684-4b0e-8b74-b080f9da7fd2
-- title:
--   Equal-label bit matches are bounded by the source LCS
-- statement:
--   Let $P>0$, let $x,y$ be words over an arbitrary alphabet, and let $f,g:\{0,\dots,N-1\}\to\mathbb N$ be strictly increasing with $\lfloor f(i)/P\rfloor<|x|$ and $\lfloor g(i)/P\rfloor<|y|$ for all $i$. If for every $i$
--   $$
--   x_{\lfloor f(i)/P\rfloor}=y_{\lfloor g(i)/P\rfloor},
--   $$
--   then $N\le P\,\mathrm{lcs}(x,y)$.
--
--   Think of $f(i)$ and $g(i)$ as matched positions in the concatenations of length-$P$ codewords of $x$ and $y$: if every matched bit pair lies in blocks carrying the same source letter, the matching has at most $P$ times as many edges as a longest common subsequence of the source words.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/CodeEqualMatches.lean#L37-L58

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

theorem OAI.TreeEdit.BinaryLower.Code.equal_label_match_count_le {α : Type*} {N P : ℕ} (hP : 0 < P)
    (x y : List α) (f g : Fin N → ℕ) (hf : StrictMono f) (hg : StrictMono g)
    (hfx : ∀ i, f i / P < x.length) (hgy : ∀ i, g i / P < y.length)
    (heq : ∀ i, x.get ⟨f i / P, hfx i⟩ = y.get ⟨g i / P, hgy i⟩) :
    N ≤ P * lcs x y := by sorry
