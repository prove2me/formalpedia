-- Prove2me | Theorems.Thm_GlobalTheory_TauValues_val_even
-- name    : GlobalTheory.TauValues.val_even
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:39:31.068723+00:00
-- url     : https://prove2.me/theorems/30db138f-e6a0-5912-a92e-6dfe6bf5db96
-- title:
--   Tau Values: val even
-- statement:
--   The Tau Values construction uses the val even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TauBimultPsiEvenOverExtensionField.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TauBimultPsiEvenOverExtensionField.lean#L60-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CorrOfValFieldExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultPsiEvenOverExtensionField
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
open GlobalTheory GlobalTheory.TauValues
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem GlobalTheory.TauValues.val_even {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) {z : T.left} {J} (hJ : Good D.P.L z J)
    (m : D.X) :
    val (LB.mulGen D.P.L _ _ _ _ (D.psi (-m)) (LB.pullGen D.P.L _ _ D.sym (D.xK m))) κ.left z J =
      val (D.psi (-m)) κ.left z J * val D.sym (cT D T m).left z J := by sorry
