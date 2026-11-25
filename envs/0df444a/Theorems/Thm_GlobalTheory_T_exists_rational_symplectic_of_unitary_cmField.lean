-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_rational_symplectic_of_unitary_cmField
-- name    : GlobalTheory.T.exists_rational_symplectic_of_unitary_cmField
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:38:53.731205+00:00
-- url     : https://prove2.me/theorems/d7cd584e-09e2-4b01-8846-1dbd0ee10eb4
-- title:
--   T: exists rational symplectic of unitary cm Field
-- statement:
--   The T construction uses the exists rational symplectic of unitary cm Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalSymplecticOfUnitaryCmFieldStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalSymplecticOfUnitaryCmFieldStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalSymplecticOfUnitaryCmField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalSymplecticOfUnitaryCmFieldStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_rational_symplectic_of_unitary_cmField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (γ : M2 E N), γ ∈ UU E N → ∃ σ ∈ Matrix.symplecticGroup (QI E N) ℚ, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ Z ∈ Hn Ψ N, spAct σ (tauOf Ψ Z) = tauOf Ψ (hAct Ψ γ Z) ∧ (spDen σ (tauOf Ψ Z)).det = c * ∏ τ, (hDen Ψ γ Z τ).det ^ 2 ∧ ∀ z z' : CM Ψ n N, (zetaOf Ψ (fun τ => Matrix.of fun k => (hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k) (fun τ => Matrix.of fun k => z' τ k ᵥ* (hDen Ψ γ Z τ)⁻¹) = fun k => zetaOf Ψ z z' k ᵥ* (spDen σ (tauOf Ψ Z))⁻¹) ∧ ∀ k, zetaOf Ψ z z' k ⬝ᵥ ((spDen σ (tauOf Ψ Z))⁻¹ * qm σ.toBlocks₂₁) *ᵥ zetaOf Ψ z z' k = 2 * ∑ τ : Ψ, z' τ k ⬝ᵥ ((hDen Ψ γ Z τ)⁻¹ * γ.toBlocks₂₁.map τ.1) *ᵥ z τ k := by sorry
