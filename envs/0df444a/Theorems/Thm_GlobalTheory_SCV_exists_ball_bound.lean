-- Prove2me | Theorems.Thm_GlobalTheory_SCV_exists_ball_bound
-- name    : GlobalTheory.SCV.exists_ball_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:54.17235+00:00
-- url     : https://prove2.me/theorems/005418a1-b770-44ad-8776-0ea842730adb
-- title:
--   SCV: exists ball bound
-- statement:
--   The SCV construction uses the exists ball bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L93-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L93-L99

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

theorem GlobalTheory.SCV.exists_ball_bound {f : E → V} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {c : E} (hc : c ∈ U) : ∃ r > 0, ∃ M : ℝ, ball c r ⊆ U ∧ ∀ z ∈ ball c r, ‖f z‖ ≤ M := by sorry
