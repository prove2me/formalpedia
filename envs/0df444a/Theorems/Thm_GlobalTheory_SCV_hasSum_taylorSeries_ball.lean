-- Prove2me | Theorems.Thm_GlobalTheory_SCV_hasSum_taylorSeries_ball
-- name    : GlobalTheory.SCV.hasSum_taylorSeries_ball
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:33:21.567178+00:00
-- url     : https://prove2.me/theorems/394debbb-1b3f-4156-862e-39c42b2f3610
-- title:
--   SCV: has Sum taylor Series ball
-- statement:
--   The SCV construction uses the has Sum taylor Series ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L237-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L237-L254

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology ContDiff Nat
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem GlobalTheory.SCV.hasSum_taylorSeries_ball {f : E → V} {c : E} {R : ℝ}
    (hf : DifferentiableOn ℂ f (ball c R)) {y : E} (hy : ‖y‖ < R) :
    HasSum (fun n : ℕ => (n ! : ℂ)⁻¹ • iteratedFDeriv ℂ n f c (fun _ => y)) (f (c + y)) := by sorry
