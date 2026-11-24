-- Prove2me | Theorems.Thm_GlobalTheory_integrableOn_log_norm_ball
-- name    : GlobalTheory.integrableOn_log_norm_ball
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:56:17.458712+00:00
-- url     : https://prove2.me/theorems/c9725c7f-dc7d-43e6-b127-7900dce0ff03
-- title:
--   Global Theory: integrable On log norm ball
-- statement:
--   The Global Theory construction uses the integrable On log norm ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegrableOnOfNormLeSumAbsLogAddLogLog.lean#L152-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegrableOnOfNormLeSumAbsLogAddLogLog.lean#L152-L169

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

theorem GlobalTheory.integrableOn_log_norm_ball (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℂ} {a : E}
    {r M : ℝ} (hf : DifferentiableOn ℂ f (ball a r)) (hM : ∀ z ∈ ball a r, ‖f z‖ ≤ M)
    (h0 : f a ≠ 0) :
    (∀ᵐ z ∂(μ.restrict (ball a r)), f z ≠ 0) ∧
      IntegrableOn (fun z => Real.log ‖f z‖) (ball a r) μ := by sorry
