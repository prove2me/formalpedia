-- Prove2me | Theorems.Thm_GlobalTheory_T_ofReal_norm_pow_mul_le_lintegral_iteratedFDeriv
-- name    : GlobalTheory.T.ofReal_norm_pow_mul_le_lintegral_iteratedFDeriv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:53:52.247663+00:00
-- url     : https://prove2.me/theorems/027f4831-c71f-498f-a898-41151b348f3d
-- title:
--   T: of Real norm pow mul le lintegral iterated FDeriv
-- statement:
--   The T construction uses the of Real norm pow mul le lintegral iterated FDeriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeightedLintegralSobolevPointwiseStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeightedLintegralSobolevPointwiseStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLintegralSobolevPointwise
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLintegralSobolevPointwiseStatement
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

theorem GlobalTheory.T.ofReal_norm_pow_mul_le_lintegral_iteratedFDeriv : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (m : ℕ), finrank ℝ E = m + 1 → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (G : E → F), ContDiff ℝ (⊤ : ℕ∞) G → (∀ j ≤ m, Tendsto (iteratedFDeriv ℝ j G) (cocompact E) (𝓝 0)) → ∀ (k : ℕ) (x : E), ENNReal.ofReal (‖x‖ ^ k * ‖G x‖) ≤ C * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ := by sorry
