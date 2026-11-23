-- Prove2me | Theorems.Thm_GlobalTheory_measurePreserving_smul_of_norm_eq_one
-- name    : GlobalTheory.measurePreserving_smul_of_norm_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:40.307313+00:00
-- url     : https://prove2.me/theorems/3c4388d4-a37f-464d-9077-40cd540d9a7d
-- title:
--   Global Theory: measure Preserving smul of norm eq one
-- statement:
--   The Global Theory construction uses the measure Preserving smul of norm eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L49-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L49-L68

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

theorem GlobalTheory.measurePreserving_smul_of_norm_eq_one (μ : Measure E) [μ.IsAddHaarMeasure] {c : ℂ}
    (hc : ‖c‖ = 1) : MeasurePreserving (fun z : E => c • z) μ μ := by sorry
