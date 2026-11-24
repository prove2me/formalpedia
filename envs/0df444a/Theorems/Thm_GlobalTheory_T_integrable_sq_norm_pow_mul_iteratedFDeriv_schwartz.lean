-- Prove2me | Theorems.Thm_GlobalTheory_T_integrable_sq_norm_pow_mul_iteratedFDeriv_schwartz
-- name    : GlobalTheory.T.integrable_sq_norm_pow_mul_iteratedFDeriv_schwartz
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:46:48.8811+00:00
-- url     : https://prove2.me/theorems/0239c06b-4398-4de9-8ed8-1bcb51b2f6a6
-- title:
--   T: integrable sq norm pow mul iterated FDeriv schwartz
-- statement:
--   The T construction uses the integrable sq norm pow mul iterated FDeriv schwartz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableSqPowMulIteratedFDerivSchwartzStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableSqPowMulIteratedFDerivSchwartzStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableSqPowMulIteratedFDerivSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableSqPowMulIteratedFDerivSchwartzStatement
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

theorem GlobalTheory.T.integrable_sq_norm_pow_mul_iteratedFDeriv_schwartz : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : SchwartzMap E F) (i j : ℕ), Integrable (fun z => (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2) μ := by sorry
