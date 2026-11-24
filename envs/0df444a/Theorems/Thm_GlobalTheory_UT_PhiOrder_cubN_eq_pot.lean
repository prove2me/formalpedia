-- Prove2me | Theorems.Thm_GlobalTheory_UT_PhiOrder_cubN_eq_pot
-- name    : GlobalTheory.UT.PhiOrder.cubN_eq_pot
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:19:51.972237+00:00
-- url     : https://prove2.me/theorems/8e1f4cf8-b92a-44e7-b48a-3414836c4ee5
-- title:
--   Phi Order: cub N eq pot
-- statement:
--   The Phi Order construction uses the cub N eq pot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SymmetricFramePhiPowOrderEqId.lean#L71-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SymmetricFramePhiPowOrderEqId.lean#L71-L80

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

theorem GlobalTheory.UT.PhiOrder.cubN_eq_pot (h : IsCub θ) (b : A) (n a c x : ℕ) :
    Additive.ofMul (cubN θ n (b ^ a) (b ^ c) (b ^ x)) = Additive.ofMul (pot θ b (a + c * n + x)) -
      Additive.ofMul (pot θ b (a + x)) - Additive.ofMul (pot θ b (a + c * n)) + Additive.ofMul (pot θ b a) -
      n • (Additive.ofMul (pot θ b (c + x)) - Additive.ofMul (pot θ b c) - Additive.ofMul (pot θ b x)) := by sorry
