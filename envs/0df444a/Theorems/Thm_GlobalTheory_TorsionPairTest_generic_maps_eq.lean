-- Prove2me | Theorems.Thm_GlobalTheory_TorsionPairTest_generic_maps_eq
-- name    : GlobalTheory.TorsionPairTest.generic_maps_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:31:47.164909+00:00
-- url     : https://prove2.me/theorems/4dffc94c-533a-4a58-9f85-50af4539a50c
-- title:
--   Torsion Pair Test: generic maps eq
-- statement:
--   The Torsion Pair Test construction uses the generic maps eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UniformisationSurvey/EquivIffOfIsEmpty.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UniformisationSurvey/EquivIffOfIsEmpty.lean#L20-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_InhTate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UniformisationSurvey_EquivIffOfIsEmpty
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionPairTest
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem GlobalTheory.TorsionPairTest.generic_maps_eq (W : (Spec (CommRingCat.of R)).Opens) (χ : D.X) :
    (jK R ∣_ W) ≫ (toUnit (TW W) ≫ D.c χ).left = (jK R ⁻¹ᵁ W).ι ≫ ptK (D.c χ) := by sorry
