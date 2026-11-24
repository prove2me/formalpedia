-- Prove2me | Theorems.Thm_GlobalTheory_HyperplaneExt_extension_across_coordinate_hyperplanes
-- name    : GlobalTheory.HyperplaneExt.extension_across_coordinate_hyperplanes
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:13:55.683251+00:00
-- url     : https://prove2.me/theorems/67bf356b-2f3e-48d2-afd9-8e98f2cee8fc
-- title:
--   Hyperplane Ext: extension across coordinate hyperplanes
-- statement:
--   The Hyperplane Ext construction uses the extension across coordinate hyperplanes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExtensionAcrossCoordinateHyperplanes.lean#L95-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExtensionAcrossCoordinateHyperplanes.lean#L95-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExtensionAcrossZeroOfExpTwoPiIBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocallyBoundedOffCoordinateHyperplanesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannExtensionCoordinateHyperplaneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExtensionAcrossCoordinateHyperplanes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Filter Topology Set
open GlobalTheory GlobalTheory.HyperplaneExt

theorem GlobalTheory.HyperplaneExt.extension_across_coordinate_hyperplanes : ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ) ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → F z = Φ z := by sorry
