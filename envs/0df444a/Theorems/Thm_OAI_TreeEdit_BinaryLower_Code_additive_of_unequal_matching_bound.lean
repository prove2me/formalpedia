-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_Code_additive_of_unequal_matching_bound
-- name    : OAI.TreeEdit.BinaryLower.Code.additive_of_unequal_matching_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:36:59.625532+00:00
-- url     : https://prove2.me/theorems/5653598b-04d1-4a2f-b683-902c821edcd7
-- title:
--   Additive deficit transfer from unequal-edge bounds on all matchings
-- statement:
--   Let $c$ assign to each letter a codeword of length $P>0$, and let $x,y$ be words of length $M$ with encodings $c(x),c(y)$ of length $MP$. Write $D(x,y)=M-\mathrm{lcs}(x,y)$ and $D(c(x),c(y))=MP-\mathrm{lcs}(c(x),c(y))$. Suppose that for every $r$ and every pair of strictly increasing $f,g:\{0,\dots,r-1\}\to\{0,\dots,MP-1\}$ with $c(x)_{f(t)}=c(y)_{g(t)}$ for all $t$, the number of indices $t$ with $x_{\lfloor f(t)/P\rfloor}\ne y_{\lfloor g(t)/P\rfloor}$ is at most $200(MP-r)+2Ma_0$. Then
--   $$
--   P\,D(x,y)\le201\,D(c(x),c(y))+2Ma_0.
--   $$
--
--   So a uniform bound on matched bit pairs joining different source letters, valid for every common subsequence of the encodings, already yields the additive deficit comparison.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/CodeAdditive.lean#L110-L130

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

theorem OAI.TreeEdit.BinaryLower.Code.additive_of_unequal_matching_bound {α : Type u} {β : Type v}
    {M P a₀ : ℕ} (c : α → Word β P) (x y : List α)
    (hx : x.length = M) (hy : y.length = M) (hP : 0 < P)
    (hunequal : ∀ (r : ℕ) (f g : Fin r → Fin (M*P)),
      StrictMono f → StrictMono g →
      (∀ t, encodedBit c x hx (f t) = encodedBit c y hy (g t)) →
      (unequalEdges x y hx hy hP f g).card ≤ 200*(M*P-r)+2*M*a₀) :
    P*deficit M x y ≤ 201*deficit (M*P) (encode c x) (encode c y)+2*M*a₀ := by sorry
