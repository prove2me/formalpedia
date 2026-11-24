-- Prove2me | Theorems.Thm_GlobalTheory_SW_exists_symplectic_of_unitary
-- name    : GlobalTheory.SW.exists_symplectic_of_unitary
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:45:12.797882+00:00
-- url     : https://prove2.me/theorems/4505449d-08ac-4cb0-9521-a07dccd4da61
-- title:
--   SW: exists symplectic of unitary
-- statement:
--   The SW construction uses the exists symplectic of unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalSymplecticOfUnitaryCmField.lean#L289-L376
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalSymplecticOfUnitaryCmField.lean#L289-L376

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalSymplecticOfUnitaryCmField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory.SW.UniSp GlobalTheory.SW.HAct Classical

theorem GlobalTheory.SW.exists_symplectic_of_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (γ : M2 E N), γ ∈ UU E N → ∃ σ ∈ Matrix.symplecticGroup (QI E N) ℚ, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ Z ∈ Hn Ψ N, spAct σ (tauOf Ψ Z) = tauOf Ψ (hAct Ψ γ Z) ∧ (spDen σ (tauOf Ψ Z)).det = c * ∏ τ, (hDen Ψ γ Z τ).det ^ 2 ∧ ∀ z z' : CM Ψ n N, (zetaOf Ψ (fun τ => Matrix.of fun k => (hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k) (fun τ => Matrix.of fun k => z' τ k ᵥ* (hDen Ψ γ Z τ)⁻¹) = fun k => zetaOf Ψ z z' k ᵥ* (spDen σ (tauOf Ψ Z))⁻¹) ∧ ∀ k, zetaOf Ψ z z' k ⬝ᵥ ((spDen σ (tauOf Ψ Z))⁻¹ * qm σ.toBlocks₂₁) *ᵥ zetaOf Ψ z z' k = 2 * ∑ τ : Ψ, z' τ k ⬝ᵥ ((hDen Ψ γ Z τ)⁻¹ * γ.toBlocks₂₁.map τ.1) *ᵥ z τ k := by sorry
