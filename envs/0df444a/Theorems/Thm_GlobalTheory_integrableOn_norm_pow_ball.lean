-- Prove2me | Theorems.Thm_GlobalTheory_integrableOn_norm_pow_ball
-- name    : GlobalTheory.integrableOn_norm_pow_ball
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:56:13.707312+00:00
-- url     : https://prove2.me/theorems/f527dad5-776f-4663-a122-dc991600149c
-- title:
--   Global Theory: integrable On norm pow ball
-- statement:
--   The Global Theory construction uses the integrable On norm pow ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L207-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L207-L212

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set
open scoped ENNReal Real
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

theorem GlobalTheory.integrableOn_norm_pow_ball {H : Type*} [NormedAddCommGroup H] (μ : Measure E)
    [μ.IsAddHaarMeasure] {a : E} {r : ℝ} {φ : E → H} (hφ : ContinuousOn φ (closedBall a r))
    (n : ℕ) : IntegrableOn (fun z => ‖φ z‖ ^ n) (ball a r) μ := by sorry
