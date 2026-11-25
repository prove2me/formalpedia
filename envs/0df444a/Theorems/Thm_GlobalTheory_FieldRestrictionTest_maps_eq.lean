-- Prove2me | Theorems.Thm_GlobalTheory_FieldRestrictionTest_maps_eq
-- name    : GlobalTheory.FieldRestrictionTest.maps_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:01:22.951893+00:00
-- url     : https://prove2.me/theorems/db58fa11-f4f2-4678-981f-4600d082af26
-- title:
--   Field Restriction Test: maps eq
-- statement:
--   The Field Restriction Test construction uses the maps eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/ExistsUniquePairIff.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/ExistsUniquePairIff.lean#L28-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_ExistsUniquePairIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FieldRestrictionTest
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {T : Over (Spec (CommRingCat.of R))}

theorem GlobalTheory.FieldRestrictionTest.maps_eq {x : Spec (CommRingCat.of F) ⟶ T.left} {g : GtPt D T} {g' : GtPtF D F}
    (H : GtPt.IsPullF F x g g') (χ : D.X) (k : Fin 4) :
    DegPre.gtφ D F g'.b χ k = x ≫ DegPre.gtφT D T g.b χ k := by sorry
