-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_intervalIntegrable_left
-- name    : GroundTheory.Global.Elliptic.intervalIntegrable_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:11.132444+00:00
-- url     : https://prove2.me/theorems/0c17bce4-3afe-4702-bf4f-ed85b34a1d42
-- title:
--   Elliptic: interval Integrable left
-- statement:
--   The Elliptic construction uses the interval Integrable left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L84-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L84-L87

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

theorem GroundTheory.Global.Elliptic.intervalIntegrable_left (hf : ContinuousOn f (rectBoundary z w)) :
    IntervalIntegrable (fun y : ℝ ↦ f (z.re + y * I)) volume z.im w.im := by sorry
