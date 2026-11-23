-- Prove2me | Theorems.Thm_GlobalTheory_SCV_differentiableOn_fderiv_apply
-- name    : GlobalTheory.SCV.differentiableOn_fderiv_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:41.449214+00:00
-- url     : https://prove2.me/theorems/38b42e83-dd17-4f78-87c8-906e15ac5f32
-- title:
--   SCV: differentiable On fderiv apply
-- statement:
--   The SCV construction uses the differentiable On fderiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L101-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L101-L144

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

theorem GlobalTheory.SCV.differentiableOn_fderiv_apply [CompleteSpace V] {f : E → V} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (v : E) :
    DifferentiableOn ℂ (fun x => fderiv ℂ f x v) U := by sorry
