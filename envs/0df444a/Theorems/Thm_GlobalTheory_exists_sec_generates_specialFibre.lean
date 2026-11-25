-- Prove2me | Theorems.Thm_GlobalTheory_exists_sec_generates_specialFibre
-- name    : GlobalTheory.exists_sec_generates_specialFibre
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:47:13.784337+00:00
-- url     : https://prove2.me/theorems/74e8f39d-8022-5a6a-afdb-0911477c0717
-- title:
--   Global Theory: exists sec generates special Fibre
-- statement:
--   The Global Theory construction uses the exists sec generates special Fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecGeneratesSpecialFibre.lean#L98-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecGeneratesSpecialFibre.lean#L98-L133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecGeneratesSpecialFibre
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
set_option backward.isDefEq.respectTransparency false
open GlobalTheory
open SpecialFibreGenerator TopologicalSpace

theorem GlobalTheory.exists_sec_generates_specialFibre : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : LB G.left), N.IsLB → ∀ s : LB.Sec (N.pull (pullback.fst G.hom (jK V))), (∃ a, a ∈ nonzeroLocus s) → IsClosed ((pullback.fst G.hom (jK V)) '' {a | a ∉ nonzeroLocus s}) → ∃ θ : H0 N 1, ∀ x : G.left, G.hom x = IsLocalRing.closedPoint V → x ∈ nonzeroLocus θ := by sorry
