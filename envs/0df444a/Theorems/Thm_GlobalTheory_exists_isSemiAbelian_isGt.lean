-- Prove2me | Theorems.Thm_GlobalTheory_exists_isSemiAbelian_isGt
-- name    : GlobalTheory.exists_isSemiAbelian_isGt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T15:27:09.946877+00:00
-- url     : https://prove2.me/theorems/821c89cb-6538-4e02-a24b-f222235bc666
-- title:
--   Global Theory: exists is Semi Abelian is Gt
-- statement:
--   The Global Theory construction uses the exists is Semi Abelian is Gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsIsSemiAbelianIsGt.lean#L17-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsIsSemiAbelianIsGt.lean#L17-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InverseBundleGeneratorPointOfChartUnitsSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGrpObjSplitExtensionOfGeneratorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyTorusExtensionOfIsGt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsIsSemiAbelianIsGt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.exists_isSemiAbelian_isGt :
    GlobalFnsSt → ∀ (S : Scheme.{0}) (E : SplitExt S),
      ∃ (G : Over S) (_ : GrpObj G), IsSemiAbelian G ∧ E.IsGt G := by sorry
