-- Prove2me | Theorems.Thm_GlobalTheory_locallyIntegrableOn_log_norm_of_frequently_ne_zero
-- name    : GlobalTheory.locallyIntegrableOn_log_norm_of_frequently_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:49:14.23595+00:00
-- url     : https://prove2.me/theorems/6e6aa90e-d46b-42f6-919d-881b2dd643be
-- title:
--   Global Theory: locally Integrable On log norm of frequently ne zero
-- statement:
--   The Global Theory construction uses the locally Integrable On log norm of frequently ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegrableOnOfNormLeSumAbsLogAddLogLog.lean#L187-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegrableOnOfNormLeSumAbsLogAddLogLog.lean#L187-L208

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

theorem GlobalTheory.locallyIntegrableOn_log_norm_of_frequently_ne_zero (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → ℂ} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hx : ∀ x ∈ U, ∃ᶠ z in 𝓝 x, f z ≠ 0) :
    (∀ᵐ z ∂(μ.restrict U), f z ≠ 0) ∧ LocallyIntegrableOn (fun z => Real.log ‖f z‖) U μ := by sorry
