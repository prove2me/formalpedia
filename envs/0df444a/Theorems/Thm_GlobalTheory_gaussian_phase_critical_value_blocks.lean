-- Prove2me | Theorems.Thm_GlobalTheory_gaussian_phase_critical_value_blocks
-- name    : GlobalTheory.gaussian_phase_critical_value_blocks
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:54:03.069821+00:00
-- url     : https://prove2.me/theorems/eead8736-d264-4b8e-b5a0-7ae0948143be
-- title:
--   Global Theory: gaussian phase critical value blocks
-- statement:
--   The Global Theory construction uses the gaussian phase critical value blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GaussianPhaseCriticalValueBlocksGeneral.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GaussianPhaseCriticalValueBlocksGeneral.lean#L75-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GaussianPhaseCriticalValueBlocksGeneral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory

theorem GlobalTheory.gaussian_phase_critical_value_blocks :
    ∀ (P Q : ℕ) (A B : Matrix (Fin P) (Fin Q) ℂ) (a c : Fin P → ℂ) (b d : Fin Q → ℂ), IsUnit (1 - Aᴴ * B).det → let S : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := fromBlocks 0 Aᴴᵀ Aᴴ 0; let T : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := fromBlocks 0 B Bᵀ 0; let w : Fin P ⊕ Fin Q → ℂ := (1 - T * S)⁻¹ *ᵥ (Sum.elim c d + T *ᵥ Sum.elim a b); let u : Fin P ⊕ Fin Q → ℂ := Sum.elim a b + S *ᵥ w; 1 / 2 * (Sum.elim a b ⬝ᵥ w + Sum.elim c d ⬝ᵥ u) = a ⬝ᵥ (1 - B * Aᴴ)⁻¹ *ᵥ c + d ⬝ᵥ (1 - Aᴴ * B)⁻¹ *ᵥ b + a ⬝ᵥ ((1 - B * Aᴴ)⁻¹ * B) *ᵥ b + d ⬝ᵥ ((1 - Aᴴ * B)⁻¹ * Aᴴ) *ᵥ c := by sorry
