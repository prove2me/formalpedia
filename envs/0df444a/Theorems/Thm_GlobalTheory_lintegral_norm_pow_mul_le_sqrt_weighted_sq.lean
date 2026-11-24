-- Prove2me | Theorems.Thm_GlobalTheory_lintegral_norm_pow_mul_le_sqrt_weighted_sq
-- name    : GlobalTheory.lintegral_norm_pow_mul_le_sqrt_weighted_sq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:07:21.571172+00:00
-- url     : https://prove2.me/theorems/8adeebc0-9316-40f8-9c0c-123f41354713
-- title:
--   Global Theory: lintegral norm pow mul le sqrt weighted sq
-- statement:
--   The Global Theory construction uses the lintegral norm pow mul le sqrt weighted sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralNormPowMulLeSqrtWeightedSq.lean#L8-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralNormPowMulLeSqrtWeightedSq.lean#L8-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralNormPowMulLeSqrtWeightedSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
open GlobalTheory

theorem GlobalTheory.lintegral_norm_pow_mul_le_sqrt_weighted_sq :
    ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] [NormedAddCommGroup F], ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (H : E → F), Continuous H → ∀ k : ℕ, ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖H z‖) ∂μ ≤ C * (∫⁻ z, ENNReal.ofReal ((‖z‖ ^ k * ‖H z‖) ^ 2) ∂μ + ∫⁻ z, ENNReal.ofReal ((‖z‖ ^ (k + finrank ℝ E + 1) * ‖H z‖) ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by sorry
