-- Prove2me | Theorems.Thm_GlobalTheory_UT_PhiOrder_const_eq_one
-- name    : GlobalTheory.UT.PhiOrder.const_eq_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:29:21.229954+00:00
-- url     : https://prove2.me/theorems/b714ac49-4d62-40ea-87d0-aa6330a3c120
-- title:
--   Phi Order: const eq one
-- statement:
--   The Phi Order construction uses the const eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SymmetricFramePhiPowOrderEqId.lean#L82-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SymmetricFramePhiPowOrderEqId.lean#L82-L130

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

theorem GlobalTheory.UT.PhiOrder.const_eq_one (h : IsCub θ) (b : A) (m k : ℕ) (hk : k = 2 * m + 1) (S : ℕ → U) (s w ψ ρ τ E : U)
    (hS : ∀ i, S i * cubN θ i 1 (b ^ k) b = s ^ i) (hτ : τ * cubN θ k 1 b (b ^ k) = s ^ k)
    (hE : τ = E * ψ ^ 2 * ρ ^ 2)
    (hw : w ^ k * ((E * pot θ b (2 * k)) ^ m * (pot θ b k ^ (k + 2 * m))⁻¹) = ψ * ρ) :
    (∏ i ∈ Finset.range k, H1.hv θ k ((b ^ k) ^ i) b (b ^ (k - 1 - i)) * (S i * w)) * (ψ ^ k * ρ ^ k)⁻¹ = 1 := by sorry
