-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_matchingSpan_inter_image
-- name    : OAI.TreeEdit.BinaryLower.matchingSpan_inter_image
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T22:31:59.077984+00:00
-- url     : https://prove2.me/theorems/986d1890-e510-49f9-901f-ff82f1729fd2
-- title:
--   A convex label span meets the matching only in its own fibre
-- statement:
--   Let $f:\{0,\dots,r-1\}\to\{0,\dots,n-1\}$ list matched positions in a word, and let $\lambda$ assign a label to each index. The fibre of a label $b$ is $F(b)=\{i:\lambda(i)=b\}$, and its span $\mathrm{Span}_f(b)$ is the set of positions $p$ with $f(i)\le p\le f(j)$ for some $i,j\in F(b)$, the interval hull of the positions labelled $b$ (empty if $F(b)$ is empty). Assume $f$ is strictly increasing and the labels are order-convex: $i\le j\le k$ and $\lambda(i)=\lambda(k)$ imply $\lambda(j)=\lambda(i)$. Then for every label $b$,
--   $$
--   \mathrm{Span}_f(b)\cap f\bigl(\{0,\dots,r-1\}\bigr)=f\bigl(F(b)\bigr).
--   $$
--
--   In words, any matched position lying inside the span of $b$ is itself labelled $b$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/MatchingSpanBudget.lean#L30-L58

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

theorem OAI.TreeEdit.BinaryLower.matchingSpan_inter_image {r n : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → Fin n) (hf : StrictMono f) (label : Fin r → β)
    (hc : ∀ {i j k}, i ≤ j → j ≤ k → label i = label k → label j = label i)
    (b : β) :
    matchingSpan f label b ∩ Finset.univ.image f =
      (Finset.univ.filter fun i => label i = b).image f := by sorry
