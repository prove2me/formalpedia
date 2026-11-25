-- Prove2me | Theorems.Thm_GlobalTheory_ThetaTranslJet_exists_completion
-- name    : GlobalTheory.ThetaTranslJet.exists_completion
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:22:42.94135+00:00
-- url     : https://prove2.me/theorems/b4111dce-20e3-47d5-be3e-2b00ee7c7c2b
-- title:
--   Theta Transl Jet: exists completion
-- statement:
--   The Theta Transl Jet construction uses the exists completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaFunctionIsogenyRestriction.lean#L258-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaFunctionIsogenyRestriction.lean#L258-L298

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImFormApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaFunctionIsogenyRestriction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ReciprocityTheory.ChartRestriction.G.I2
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaTranslJet
variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}

theorem GlobalTheory.ThetaTranslJet.exists_completion {Λ : AddSubgroup (Fin g → ℂ)} {χ θ : (Fin g → ℂ) → ℂ}
    (hd : Differentiable ℂ θ) (h0 : θ ≠ 0)
    (hθ : ∀ a ∈ Λ, ∀ z, θ (z + a) = χ a * Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec z) +
      Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a)) * θ z) (M : ℕ) (S : Fin g → ℂ) {κ : Type}
    (t : Finset κ) (x : κ → Fin g → ℂ) (ht : t.card + 2 ≤ M) :
    ∃ h : (Fin g → ℂ) → ℂ, Differentiable ℂ h ∧ h 0 ≠ 0 ∧ ∀ a ∈ Λ, ∀ z,
      (∏ j ∈ t, θ (z + a + x j)) * h (z + a) = χ a ^ M *
        Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec S - star S ⬝ᵥ Hm.mulVec a)) *
        Complex.exp (M * (Real.pi * (star a ⬝ᵥ Hm.mulVec z) +
          Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a))) * ((∏ j ∈ t, θ (z + x j)) * h z) := by sorry
