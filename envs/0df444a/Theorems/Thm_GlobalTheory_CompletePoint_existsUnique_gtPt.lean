-- Prove2me | Theorems.Thm_GlobalTheory_CompletePoint_existsUnique_gtPt
-- name    : GlobalTheory.CompletePoint.existsUnique_gtPt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:33:00.253161+00:00
-- url     : https://prove2.me/theorems/5ad30fbd-4ad2-58c0-a9c8-e99aebb17039
-- title:
--   Complete Point: exists Unique gt Pt
-- statement:
--   The Complete Point construction uses the exists Unique gt Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUniqueTorusExtensionPointOfGroupPoint.lean#L153-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUniqueTorusExtensionPointOfGroupPoint.lean#L153-L213

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueTorusExtensionPointOfGroupPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompletePoint
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
variable [IsLocalRing R] [IsAdicComplete I R] {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem GlobalTheory.CompletePoint.existsUnique_gtPt (y : ∀ e, Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left)
    (hw : ∀ e, y e ≫ (thickObj R I e G).hom = 𝟙 _)
    (hy : ∀ e, thickTrans R I e ≫ y (e + 1) = y e ≫ thickMap R I e G) :
    ∃! gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R)))), ∀ e,
      thick R I e ≫ gp.b.left = y e ≫ (U.gt e).pG.left ∧ ∀ χ z J, Good D.toPre.P.L z J →
        val (Y := Spec (CommRingCat.of R)) (gp.s χ) (thick R I e) z J = val ((U.gt e).t χ) (y e) z J := by sorry
