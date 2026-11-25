-- Prove2me | Theorems.Thm_GlobalTheory_ThetaSpecialise_secScal_one_iff
-- name    : GlobalTheory.ThetaSpecialise.secScal_one_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:34:31.523387+00:00
-- url     : https://prove2.me/theorems/7cfa661f-7e04-4596-9f94-57e8c24406fd
-- title:
--   Theta Specialise: sec Scal one iff
-- statement:
--   The Theta Specialise construction uses the sec Scal one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PowEqOneOfInjective.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PowEqOneOfInjective.lean#L69-L73

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsFOfIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfInjective
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
variable {X X' X'' Y Y' Y'' Y₁ Y₁' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {Φ : X' ⟶ X} {Φ' : X'' ⟶ X'}
  {K : Type} [Fintype K] {ε : K → ℤ}
variable {φ : K → (Y ⟶ X)} {φ₁ : K → (Y₁ ⟶ X)} {φ₂ : K → (Y₁' ⟶ X)} {a : Y₁ ⟶ Y} {b : Y₁' ⟶ Y₁}
  {s : LB.Sec (LB.LinComb L φ ε)} {t : LB.Sec (LB.LinComb L φ₁ ε)} {v : LB.Sec (LB.LinComb L φ₂ ε)}

theorem GlobalTheory.ThetaSpecialise.secScal_one_iff (hL : L.IsLB) : GeneratorPullback.SecScal L φ₁ ε t φ ε s a 1 ↔
    ∀ y J, Good L y J → Geo.Tor.sval s (𝟙 Y₁ ≫ a) y J = Geo.Tor.sval t (𝟙 Y₁) y J := by sorry
