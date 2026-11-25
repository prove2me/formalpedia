-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_torsion_lift
-- name    : GlobalTheory.existsUnique_torsion_lift
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:02:59.81191+00:00
-- url     : https://prove2.me/theorems/170e43ff-bd72-4793-85d4-19b6adb75e49
-- title:
--   Global Theory: exists Unique torsion lift
-- statement:
--   The Global Theory construction uses the exists Unique torsion lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUniqueOfIsAdicComplete.lean#L236-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUniqueOfIsAdicComplete.lean#L236-L272

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteOfIsClosedSplitTorusOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueOfIsAdicComplete
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id)
open IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open TorsionLift

theorem GlobalTheory.existsUnique_torsion_lift (W : Type) [CommRing W] [IsLocalRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W] (S : Scheme.{0}) (G : Over S) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] (p : Spec (CommRingCat.of W) ⟶ S) (N : ℕ)
    (hN : IsUnit (N : W))
    (x₀ : Over.mk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue W)) ≫ p) ⟶ G)
    (hx₀ : x₀ ^ N = 1) : ∃! x : Over.mk p ⟶ G, x ^ N = 1 ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue W)) ≫ x.left = x₀.left := by sorry
