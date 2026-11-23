-- Prove2me | Theorems.Thm_GlobalTheory_SCV_analyticOnNhd_of_differentiable
-- name    : GlobalTheory.SCV.analyticOnNhd_of_differentiable
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:06.378804+00:00
-- url     : https://prove2.me/theorems/ad4a1c41-4a05-45b5-9f0d-9ff646d10f7c
-- title:
--   SCV: analytic On Nhd of differentiable
-- statement:
--   The SCV construction uses the analytic On Nhd of differentiable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L305-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L305-L307

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

theorem GlobalTheory.SCV.analyticOnNhd_of_differentiable {f : E → V} (hf : Differentiable ℂ f) (s : Set E) :
    AnalyticOnNhd ℂ f s := by sorry
