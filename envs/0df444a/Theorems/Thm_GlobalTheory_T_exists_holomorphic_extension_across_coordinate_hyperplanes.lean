-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_holomorphic_extension_across_coordinate_hyperplanes
-- name    : GlobalTheory.T.exists_holomorphic_extension_across_coordinate_hyperplanes
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:30:22.416707+00:00
-- url     : https://prove2.me/theorems/5f3eaf54-fbe1-461f-afbe-c5ef6ef2c14c
-- title:
--   T: exists holomorphic extension across coordinate hyperplanes
-- statement:
--   The T construction uses the exists holomorphic extension across coordinate hyperplanes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExtensionAcrossCoordinateHyperplanesStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExtensionAcrossCoordinateHyperplanesStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExtensionAcrossCoordinateHyperplanes
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExtensionAcrossCoordinateHyperplanesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_holomorphic_extension_across_coordinate_hyperplanes : ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ) ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → F z = Φ z := by sorry
