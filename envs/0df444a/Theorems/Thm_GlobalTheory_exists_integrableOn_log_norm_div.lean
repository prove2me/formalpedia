-- Prove2me | Theorems.Thm_GlobalTheory_exists_integrableOn_log_norm_div
-- name    : GlobalTheory.exists_integrableOn_log_norm_div
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:45:14.539806+00:00
-- url     : https://prove2.me/theorems/56b0ac0c-5a6e-4327-bfc2-da6d08583ac4
-- title:
--   Global Theory: exists integrable On log norm div
-- statement:
--   The Global Theory construction uses the exists integrable On log norm div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegrableOnOfNormLeSumAbsLogAddLogLog.lean#L210-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegrableOnOfNormLeSumAbsLogAddLogLog.lean#L210-L224

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

theorem GlobalTheory.exists_integrableOn_log_norm_div (μ : Measure E) [μ.IsAddHaarMeasure]
    {g h : E → ℂ} {x : E} (hg : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ g z)
    (hh : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ h z) (hg0 : ∃ᶠ z in 𝓝 x, g z ≠ 0)
    (hh0 : ∃ᶠ z in 𝓝 x, h z ≠ 0) :
    ∃ r > 0, (∀ᵐ z ∂(μ.restrict (ball x r)), g z ≠ 0 ∧ h z ≠ 0) ∧
      IntegrableOn (fun z => Real.log ‖g z / h z‖) (ball x r) μ := by sorry
