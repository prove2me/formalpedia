-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_Code_additive_of_longest_unequal_bound
-- name    : OAI.TreeEdit.BinaryLower.Code.additive_of_longest_unequal_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:35:24.755884+00:00
-- url     : https://prove2.me/theorems/47ac484a-a6b0-4889-87ef-43274938f6c3
-- title:
--   Additive deficit transfer from a bound on unequal-label edges
-- statement:
--   Let $c$ assign to each letter of an alphabet a codeword of length $P>0$, and let $x,y$ be words of length $M$ with encodings $c(x),c(y)$ of length $MP$ (concatenated codewords). Write $D(x,y)=M-\mathrm{lcs}(x,y)$ and $D(c(x),c(y))=MP-\mathrm{lcs}(c(x),c(y))$ for the deficits. Let $f,g:\{0,\dots,r-1\}\to\{0,\dots,MP-1\}$ be strictly increasing, where $r=\mathrm{lcs}(c(x),c(y))$, and call an index $t$ unequal when the source letters $x_{\lfloor f(t)/P\rfloor}$ and $y_{\lfloor g(t)/P\rfloor}$ differ. If the number of unequal indices is at most $200\,D(c(x),c(y))+2Ma_0$, then
--   $$
--   P\,D(x,y)\le201\,D(c(x),c(y))+2Ma_0.
--   $$
--
--   Once the matched bit pairs joining different source letters are controlled, the source deficit scaled by the block length is bounded by the encoded deficit, up to an additive error from short segments.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/CodeAdditive.lean#L66-L108

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Code
universe u v

theorem OAI.TreeEdit.BinaryLower.Code.additive_of_longest_unequal_bound {α : Type u} {β : Type v}
    {M P a₀ : ℕ} (c : α → Word β P) (x y : List α)
    (hx : x.length = M) (hy : y.length = M) (hP : 0 < P)
    (f g : Fin (lcs (encode c x) (encode c y)) → Fin (M*P))
    (hf : StrictMono f) (hg : StrictMono g)
    (hunequal : (unequalEdges x y hx hy hP f g).card ≤
      200*(M*P-lcs (encode c x) (encode c y))+2*M*a₀) :
    P*deficit M x y ≤ 201*deficit (M*P) (encode c x) (encode c y)+2*M*a₀ := by sorry
