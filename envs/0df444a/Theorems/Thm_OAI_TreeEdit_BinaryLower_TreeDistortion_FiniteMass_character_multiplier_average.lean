-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_TreeDistortion_FiniteMass_character_multiplier_average
-- name    : OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.character_multiplier_average
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:29:56.553226+00:00
-- url     : https://prove2.me/theorems/8753c821-12ef-4a66-a993-f5c9b0a4ccd6
-- title:
--   Average of the translation multiplier of a character
-- statement:
--   Let $A$ be a finite abelian group and $\chi$ a character of $A$. Then
--   $$
--   \frac1{|A|}\sum_{z\in A}|1-\chi(z)|^2=\begin{cases}0,&\chi\text{ trivial},\\2,&\text{otherwise}.\end{cases}
--   $$
--
--   Averaged over all translations, a nontrivial character sees a multiplier of $2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/SparseActivity.lean#L300-L319

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open scoped BigOperators
open Classical

theorem OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.character_multiplier_average {A : Type*} [AddCommGroup A] [Fintype A]
    (χ : AddChar A ℂ) :
    (∑ z : A, ‖1 - χ z‖ ^ 2) / (Fintype.card A : ℝ) =
      if χ = 0 then 0 else 2 := by sorry
