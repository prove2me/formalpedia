-- Prove2me | Theorems.Thm_GlobalTheory_ThetaTranslJet_exists_translates_jet_ne_zero
-- name    : GlobalTheory.ThetaTranslJet.exists_translates_jet_ne_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:28:56.294638+00:00
-- url     : https://prove2.me/theorems/ea90b650-3a8d-5af5-86ef-f6c4a70a317e
-- title:
--   Theta Transl Jet: exists translates jet ne zero
-- statement:
--   The Theta Transl Jet construction uses the exists translates jet ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaFunctionIsogenyRestriction.lean#L325-L429
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaFunctionIsogenyRestriction.lean#L325-L429

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

theorem GlobalTheory.ThetaTranslJet.exists_translates_jet_ne_zero : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.PosDef → ∀ (Λ : AddSubgroup (Fin g → ℂ)), DiscreteTopology Λ → (∀ v, (∀ a ∈ Λ, ∃ k : ℤ, (star v ⬝ᵥ Hm.mulVec a).im = k) ↔ v ∈ Λ) → ∀ (χ θ : (Fin g → ℂ) → ℂ), Differentiable ℂ θ → θ ≠ 0 → (∀ a ∈ Λ, ‖χ a‖ = 1) → (∀ a ∈ Λ, ∀ z, θ (z + a) = χ a * Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec z) + Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a)) * θ z) → ∀ (M : ℕ) (Λ₁ : AddSubgroup (Fin g → ℂ)), Λ₁ ≤ Λ → (∀ v, (∀ a ∈ Λ₁, ∃ k : ℤ, (star v ⬝ᵥ Hm.mulVec a).im = M * k) ↔ v ∈ Λ₁) → ∀ (n : ℕ) (P : MvPolynomial (Fin n × Fin g) ℂ), P ≠ 0 → P.totalDegree + 2 ≤ M → ∃ y : Fin n → Fin g → ℂ, (∀ b, (M : ℂ) • y b ∈ Λ₁) ∧ ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (fun q => (Pi.single q.1 (Pi.single q.2 (1 : ℂ) : Fin g → ℂ) : Fin n → Fin g → ℂ)) (fun z : Fin n → Fin g → ℂ => ∏ b, Complex.exp (-(Real.pi * (star (y b) ⬝ᵥ Hm.mulVec (z b)))) * θ (z b + y b)) 0 ≠ 0 := by sorry
