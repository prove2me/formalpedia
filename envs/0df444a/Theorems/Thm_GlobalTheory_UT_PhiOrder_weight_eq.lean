-- Prove2me | Theorems.Thm_GlobalTheory_UT_PhiOrder_weight_eq
-- name    : GlobalTheory.UT.PhiOrder.weight_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:20:34.649635+00:00
-- url     : https://prove2.me/theorems/ac953824-9b30-4cd6-91b8-e3f3c431cd9f
-- title:
--   Phi Order: weight eq
-- statement:
--   The Phi Order construction uses the weight eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SymmetricFramePhiPowOrderEqId.lean#L154-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SymmetricFramePhiPowOrderEqId.lean#L154-L166

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
variable {A U : Type} [CommGroup A] [CommGroup U]

theorem GlobalTheory.UT.PhiOrder.weight_eq (h : A → U) (x : A) (m k : ℕ) (hk : k = 2 * m + 1) :
    ((h (x ^ k * (x ^ k)⁻¹ * x ^ k) * (h (x ^ k * (x ^ k)⁻¹))⁻¹ * (h (x ^ k * x ^ k))⁻¹ * (h ((x ^ k)⁻¹ * x ^ k))⁻¹ *
        h (x ^ k) * h (x ^ k)⁻¹ * h (x ^ k) * (h 1)⁻¹ * (h (x ^ k)⁻¹ * (h (x ^ k))⁻¹)⁻¹) *
        ∏ j ∈ Finset.range (2 * k), wN h x j) ^ m * ((∏ j ∈ Finset.range k, wN h x j) ^ (k + 2 * m))⁻¹ =
      h x ^ ((k ^ 2 : ℕ) : ℤ) * h (x ^ k) ^ (-((1 : ℕ) : ℤ)) * h 1 ^ (((1 : ℕ) : ℤ) - (k ^ 2 : ℕ)) := by sorry
