-- Prove2me | Theorems.Thm_GlobalTheory_FockRep_exists_unitary_osc
-- name    : GlobalTheory.FockRep.exists_unitary_osc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:00.4488+00:00
-- url     : https://prove2.me/theorems/e12973b7-f4bd-4943-947d-12898fec1e9a
-- title:
--   Fock Rep: exists unitary osc
-- statement:
--   The Fock Rep construction uses the exists unitary osc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryOsc.lean#L120-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryOsc.lean#L120-L293

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfOrthogonalTranslatesProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianPairingUnitaryGroupTwoThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryOsc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Matrix MeasureTheory Complex GlobalTheory.RealWeil GlobalTheory.RealWeil.UnitaryOsc
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.FockRep
open Matrix MeasureTheory Complex
open scoped InnerProductSpace

theorem GlobalTheory.FockRep.exists_unitary_osc : ∀ (p q : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : (Fin p ⊕ Fin q → ℂ) → (H ≃ₗᵢ[ℂ] H)), (∀ v, Continuous fun z => ρ z v) → (∀ z w v, ρ z (ρ w v) = Complex.exp (Real.pi * Complex.I * ((∑ i, z (Sum.inl i) * star (w (Sum.inl i))) - ∑ j, z (Sum.inr j) * star (w (Sum.inr j))).im) • ρ (z + w) v) → ∃ ω : _root_.GlobalTheory.WeilM.UG (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) (Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1 : Matrix (Fin q) (Fin q) ℂ)) →* (H ≃ₗᵢ[ℂ] H), (∀ v, Continuous fun g => ω g v) ∧ (∀ g z v, ω g (ρ z v) = ρ ((g.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ z) (ω g v)) ∧ (∀ A : H →L[ℂ] H, (∀ z v, A (ρ z v) = ρ z (A v)) → ∀ g v, A (ω g v) = ω g (A v)) ∧ ∀ g, (g.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₂ = 0 → (g.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₁ = 0 → ∀ v, (∀ z, ⟪v, ρ z v⟫_ℂ = Complex.exp (-(Real.pi / 2) * ∑ a, ((‖z a‖ ^ 2 : ℝ) : ℂ)) * ⟪v, v⟫_ℂ) → ω g v = (g.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁.det • v := by sorry
