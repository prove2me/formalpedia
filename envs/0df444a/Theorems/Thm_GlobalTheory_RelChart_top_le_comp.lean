-- Prove2me | Theorems.Thm_GlobalTheory_RelChart_top_le_comp
-- name    : GlobalTheory.RelChart.top_le_comp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:23:58.915288+00:00
-- url     : https://prove2.me/theorems/b6dcde35-87c5-413e-bc4b-c6a1fa8eefe5
-- title:
--   Rel Chart: top le comp
-- statement:
--   The Rel Chart construction uses the top le comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsChartWithParameters.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsChartWithParameters.lean#L25-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsChartWithParameters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.RelChart
open GlobalTheory.TangentOrigin

theorem GlobalTheory.RelChart.top_le_comp {R : Type} [CommRing R] {X Y : Scheme.{0}} (v : Sp R ⟶ X) (φ : X ⟶ Y) {U : Y.Opens}
    {V : X.Opens} (e : V ≤ φ ⁻¹ᵁ U) (hV : ⊤ ≤ v ⁻¹ᵁ V) : ⊤ ≤ (v ≫ φ) ⁻¹ᵁ U := by sorry
