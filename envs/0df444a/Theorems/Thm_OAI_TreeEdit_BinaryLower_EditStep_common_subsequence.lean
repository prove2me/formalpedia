-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_EditStep_common_subsequence
-- name    : OAI.TreeEdit.BinaryLower.EditStep.common_subsequence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:17:48.226986+00:00
-- url     : https://prove2.me/theorems/cfa36321-59ca-4da6-af1d-178c92ef2fd1
-- title:
--   One edit step keeps a long common subsequence
-- statement:
--   Here $\mathrm{ed}(x,y)$ is the unit-cost edit distance (insertions, deletions, substitutions), $\mathrm{lcs}(x,y)$ the length of a longest common subsequence, and for words of length $n$ the deficit is $n-\mathrm{lcs}(x,y)$. If $y$ is obtained from $x$ by one insertion, deletion or substitution, then there is a common sublist $z$ of $x$ and $y$ with
--   $$
--   |x|+|y|\le2+2|z| .
--   $$
--
--   Iterating this gives that the deficit of equal-length words is at most their edit distance.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/EditLCSLower.lean#L9-L31

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower

theorem OAI.TreeEdit.BinaryLower.EditStep.common_subsequence {α : Type*} {x y : List α}
    (h : EditStep x y) :
    ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧
      x.length + y.length ≤ 2 + 2 * z.length := by sorry
