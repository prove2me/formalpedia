-- Prove2me | Theorems.Thm_GlobalTheory_exists_integrableOn_log_norm_of_frequently_ne_zero
-- name    : GlobalTheory.exists_integrableOn_log_norm_of_frequently_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:37.016178+00:00
-- url     : https://prove2.me/theorems/027d2b33-6156-4475-b316-ab2871059b10
-- title:
--   Global Theory: exists integrable On log norm of frequently ne zero
-- statement:
--   The Global Theory construction uses the exists integrable On log norm of frequently ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegrableOnOfNormLeSumAbsLogAddLogLog.lean#L171-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegrableOnOfNormLeSumAbsLogAddLogLog.lean#L171-L185

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableOnOfNormLeSumAbsLogAddLogLog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal Real
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]

theorem GlobalTheory.exists_integrableOn_log_norm_of_frequently_ne_zero (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → ℂ} {x : E} (hf : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ f z) (hx : ∃ᶠ z in 𝓝 x, f z ≠ 0) :
    ∃ r > 0, (∀ᵐ z ∂(μ.restrict (ball x r)), f z ≠ 0) ∧
      IntegrableOn (fun z => Real.log ‖f z‖) (ball x r) μ := by sorry
