-- Prove2me | Theorems.Thm_GlobalTheory_integrable_sq_pow_mul_iteratedFDeriv_schwartz
-- name    : GlobalTheory.integrable_sq_pow_mul_iteratedFDeriv_schwartz
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:56:26.010132+00:00
-- url     : https://prove2.me/theorems/c49722a7-70e4-4656-91bf-3da61bb7cb7c
-- title:
--   Global Theory: integrable sq pow mul iterated FDeriv schwartz
-- statement:
--   The Global Theory construction uses the integrable sq pow mul iterated FDeriv schwartz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableSqPowMulIteratedFDerivSchwartz.lean#L8-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableSqPowMulIteratedFDerivSchwartz.lean#L8-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableSqPowMulIteratedFDerivSchwartz
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

theorem GlobalTheory.integrable_sq_pow_mul_iteratedFDeriv_schwartz
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : SchwartzMap E F) (i j : ℕ) :
    Integrable (fun z => (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2) μ := by sorry
