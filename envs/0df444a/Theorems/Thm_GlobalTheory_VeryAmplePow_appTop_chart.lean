-- Prove2me | Theorems.Thm_GlobalTheory_VeryAmplePow_appTop_chart
-- name    : GlobalTheory.VeryAmplePow.appTop_chart
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:50:31.205728+00:00
-- url     : https://prove2.me/theorems/e7aad7be-f92d-4e5d-8705-f154f88d7014
-- title:
--   Very Ample Pow: app Top chart
-- statement:
--   The Very Ample Pow construction uses the app Top chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L22-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L22-L33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VeryAmplePow
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

theorem GlobalTheory.VeryAmplePow.appTop_chart {Y Z : Scheme.{0}} (D : Y.Opens) {B : CommRingCat.{0}} (φ : B ⟶ Γ(Y, D))
    (g : Z ⟶ D.toScheme) :
    (g ≫ D.toSpecΓ ≫ Spec.map φ).appTop =
      (Scheme.ΓSpecIso B).hom ≫ φ ≫ (g ≫ D.ι).appLE D ⊤ (le_pre D g) := by sorry
