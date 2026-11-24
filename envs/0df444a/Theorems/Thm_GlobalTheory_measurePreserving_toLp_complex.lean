-- Prove2me | Theorems.Thm_GlobalTheory_measurePreserving_toLp_complex
-- name    : GlobalTheory.measurePreserving_toLp_complex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:54.826076+00:00
-- url     : https://prove2.me/theorems/3f5b2332-fe12-4dd5-ac80-12f1982f08b2
-- title:
--   Global Theory: measure Preserving to Lp complex
-- statement:
--   The Global Theory construction uses the measure Preserving to Lp complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L289-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L289-L316

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
variable {ι : Type*} [Fintype ι]

theorem GlobalTheory.measurePreserving_toLp_complex :
    MeasurePreserving (WithLp.toLp 2 : (ι → ℂ) → EuclideanSpace ℂ ι) := by sorry
