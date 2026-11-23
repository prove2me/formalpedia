-- Prove2me | Theorems.Thm_GlobalTheory_SCV_norm_sub_sub_fderiv_le_of_ball
-- name    : GlobalTheory.SCV.norm_sub_sub_fderiv_le_of_ball
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:07.601222+00:00
-- url     : https://prove2.me/theorems/3083c6de-cb18-4fb4-a972-b3fb4fd4faed
-- title:
--   SCV: norm sub sub fderiv le of ball
-- statement:
--   The SCV construction uses the norm sub sub fderiv le of ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L21-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L21-L48

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
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem GlobalTheory.SCV.norm_sub_sub_fderiv_le_of_ball {f : E → V} {c z : E} {r M : ℝ}
    (hf : DifferentiableOn ℂ f (ball c r)) (hM : ∀ z ∈ ball c r, ‖f z‖ ≤ M)
    (hz : z ∈ ball c r) :
    ‖f z - f c - fderiv ℂ f c (z - c)‖ ≤ 4 * M * (‖z - c‖ / r) ^ 2 := by sorry
