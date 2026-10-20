-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_matchingSpan_exists_endpoints
-- name    : OAI.TreeEdit.BinaryLower.matchingSpan_exists_endpoints
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:46:15.739789+00:00
-- url     : https://prove2.me/theorems/77f31fa0-1ad1-4785-a9b8-04c3d723dc7b
-- title:
--   A nonempty label span is the interval between its extreme matches
-- statement:
--   Let $f:\{0,\dots,r-1\}\to\{0,\dots,n-1\}$ list matched positions in a word, and let $\lambda$ assign a label to each index. The fibre of a label $b$ is $F(b)=\{i:\lambda(i)=b\}$, and its span $\mathrm{Span}_f(b)$ is the set of positions $p$ with $f(i)\le p\le f(j)$ for some $i,j\in F(b)$, the interval hull of the positions labelled $b$ (empty if $F(b)$ is empty). Assume only that $f$ is monotone, and let $b$ be a label with $F(b)$ nonempty. Then there are $i\le j$ in $F(b)$ such that
--   $$
--   \mathrm{Span}_f(b)=[f(i),f(j)],\qquad|\mathrm{Span}_f(b)|=f(j)+1-f(i).
--   $$
--
--   The span is the full integer interval between the first and last matched positions with label $b$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/MatchingSpanBudget.lean#L171-L192

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower

theorem OAI.TreeEdit.BinaryLower.matchingSpan_exists_endpoints {r n : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → Fin n) (hf : Monotone f) (label : Fin r → β)
    (b : β) (hex : ∃ i, label i = b) :
    ∃ i j, label i = b ∧ label j = b ∧ i ≤ j ∧
      matchingSpan f label b = Finset.Icc (f i) (f j) ∧
      (matchingSpan f label b).card = (f j).val + 1 - (f i).val := by sorry
