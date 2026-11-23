-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_intervalIntegrable_bottom
-- name    : GroundTheory.Global.Elliptic.intervalIntegrable_bottom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:07.489325+00:00
-- url     : https://prove2.me/theorems/11cbaf57-34c3-4659-9ee2-b281775d5581
-- title:
--   Elliptic: interval Integrable bottom
-- statement:
--   The Elliptic construction uses the interval Integrable bottom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L66-L69

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Real MeasureTheory Filter Topology intervalIntegral
open scoped Interval
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {z w : ℂ}
variable {f g : ℂ → E}
omit [NormedSpace ℂ E]

theorem GroundTheory.Global.Elliptic.intervalIntegrable_bottom (hf : ContinuousOn f (rectBoundary z w)) :
    IntervalIntegrable (fun x : ℝ ↦ f (x + z.im * I)) volume z.re w.re := by sorry
