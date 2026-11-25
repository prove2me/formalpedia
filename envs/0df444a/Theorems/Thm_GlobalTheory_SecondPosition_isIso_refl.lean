-- Prove2me | Theorems.Thm_GlobalTheory_SecondPosition_isIso_refl
-- name    : GlobalTheory.SecondPosition.isIso_refl
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:43:23.926017+00:00
-- url     : https://prove2.me/theorems/49a3afcd-759a-4f6a-8928-9c829470e530
-- title:
--   Second Position: is Iso refl
-- statement:
--   The Second Position construction uses the is Iso refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PsiMulPsiOfAdditionSecondVariable.lean#L101-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PsiMulPsiOfAdditionSecondVariable.lean#L101-L109

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalNeZeroOfIsIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValuesNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsIntegralTensorLeftOfSmoothGrpObj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiMulPsiOfAdditionFirstVariable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiMulPsiOfAdditionSecondVariable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory
open GlobalTheory.SecondPosition
open FirstSlot
variable {R : Type} [CommRing R] [IsDomain R]

theorem GlobalTheory.SecondPosition.isIso_refl (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (χ : D.X) :
    IsIso (lift (fst T D.P.A) ((snd T D.P.A)⁻¹ * cT D (T ⊗ D.P.A) χ)) := by sorry
