-- Prove2me | Theorems.Thm_GlobalTheory_ThetaSpecialise_gs_pullOver
-- name    : GlobalTheory.ThetaSpecialise.gs_pullOver
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:20:08.592279+00:00
-- url     : https://prove2.me/theorems/efb89ad7-7b7f-4666-8cbc-b70c619f6075
-- title:
--   Theta Specialise: gs pull Over
-- statement:
--   The Theta Specialise construction uses the gs pull Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpandsFOfIntegral.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpandsFOfIntegral.lean#L29-L35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsMoveMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsFOfIntegral
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
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaSpecialise
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
  GlobalTheory.ThetaBaseChange

theorem GlobalTheory.ThetaSpecialise.gs_pullOver {R R' : Type} [CommRing R] [CommRing R'] {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {π : Y ⟶ Spec (CommRingCat.of R)} {π' : Y' ⟶ Spec (CommRingCat.of R')}
    {f : R →+* R'} {p : Y' ⟶ Y} (hp : p ≫ π = π' ≫ Spec.map (CommRingCat.ofHom f)) {φ' : K → (Y' ⟶ X)}
    (hφ : ∀ k, φ' k = p ≫ φ k) (s : SecOver π (LB.LinComb L φ ε)) (r : Z ⟶ Y') (z : Z) (j : K → L.ι)
    (hj : ∀ k, φ' k (r z) ∈ L.U (j k)) :
    gs r z (LB.wchart L φ' j) (LB.Sec.f (pullOver L ε hp hφ s) j) = gs (r ≫ p) z (LB.wchart L φ j) (LB.Sec.f s j) := by sorry
