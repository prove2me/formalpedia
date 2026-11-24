-- Prove2me | Theorems.Thm_GlobalTheory_UT_PhiOrder_cub_eq_pot
-- name    : GlobalTheory.UT.PhiOrder.cub_eq_pot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:29.850807+00:00
-- url     : https://prove2.me/theorems/11c97a3c-1092-4f71-9090-380dc1da17a8
-- title:
--   Phi Order: cub eq pot
-- statement:
--   The Phi Order construction uses the cub eq pot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SymmetricFramePhiPowOrderEqId.lean#L33-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SymmetricFramePhiPowOrderEqId.lean#L33-L69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SymmetricFramePhiPowOrderEqId
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.PhiOrder
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

theorem GlobalTheory.UT.PhiOrder.cub_eq_pot (h : IsCub θ) (b : A) (i j l : ℕ) :
    Additive.ofMul (θ (b ^ i) (b ^ j) (b ^ l)) = Additive.ofMul (pot θ b (i + j + l)) - Additive.ofMul (pot θ b (i + j)) -
      Additive.ofMul (pot θ b (i + l)) - Additive.ofMul (pot θ b (j + l)) + Additive.ofMul (pot θ b i) +
      Additive.ofMul (pot θ b j) + Additive.ofMul (pot θ b l) := by sorry
