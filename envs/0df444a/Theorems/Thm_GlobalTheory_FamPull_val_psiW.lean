-- Prove2me | Theorems.Thm_GlobalTheory_FamPull_val_psiW
-- name    : GlobalTheory.FamPull.val_psiW
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:19:06.908999+00:00
-- url     : https://prove2.me/theorems/d1346849-858b-4c95-b00b-ed49b92986f6
-- title:
--   Fam Pull: val psi W
-- statement:
--   The Fam Pull construction uses the val psi W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFamOfIsPullDeg.lean#L219-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFamOfIsPullDeg.lean#L219-L239

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFamOfIsPullDeg
import Theorems.Thm_GlobalTheory_TauPull_val_psiW

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
noncomputable section
open GlobalTheory
open GlobalTheory.FamPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem GlobalTheory.FamPull.val_psiW (hD : IsPullDeg φ D D') {Z : Scheme.{0}} (r : Z ⟶ (TK R').left) {y : Z} {J J'}
    (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J') (χ : D'.X) : val (hD.psiW.psi (hD.xe χ)) (r ≫ hD.g) y J =
      (gw hD.w (r ≫ D'.xK χ) y (J ((r ≫ D'.xK χ) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
        (J' (r ≫ D'.xK χ)))⁻¹ * val (D'.psi χ) r y J' := by sorry
