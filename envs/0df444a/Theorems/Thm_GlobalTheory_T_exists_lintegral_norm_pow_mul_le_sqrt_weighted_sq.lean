-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_lintegral_norm_pow_mul_le_sqrt_weighted_sq
-- name    : GlobalTheory.T.exists_lintegral_norm_pow_mul_le_sqrt_weighted_sq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:36:44.313368+00:00
-- url     : https://prove2.me/theorems/b461797a-725e-41af-a6ac-ebed53cc659d
-- title:
--   T: exists lintegral norm pow mul le sqrt weighted sq
-- statement:
--   The T construction uses the exists lintegral norm pow mul le sqrt weighted sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralNormPowMulLeSqrtWeightedSqStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralNormPowMulLeSqrtWeightedSqStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralNormPowMulLeSqrtWeightedSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralNormPowMulLeSqrtWeightedSqStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_lintegral_norm_pow_mul_le_sqrt_weighted_sq : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] [NormedAddCommGroup F], ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (H : E → F), Continuous H → ∀ k : ℕ, ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖H z‖) ∂μ ≤ C * (∫⁻ z, ENNReal.ofReal ((‖z‖ ^ k * ‖H z‖) ^ 2) ∂μ + ∫⁻ z, ENNReal.ofReal ((‖z‖ ^ (k + finrank ℝ E + 1) * ‖H z‖) ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by sorry
