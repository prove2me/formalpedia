-- Prove2me | Theorems.Thm_GlobalTheory_SCV_analyticOnNhd_iff_differentiableOn
-- name    : GlobalTheory.SCV.analyticOnNhd_iff_differentiableOn
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:20:43.35007+00:00
-- url     : https://prove2.me/theorems/f7686f8f-a87f-40cd-8059-0fb99b597b37
-- title:
--   SCV: analytic On Nhd iff differentiable On
-- statement:
--   The SCV construction uses the analytic On Nhd iff differentiable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L290-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L290-L292

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

theorem GlobalTheory.SCV.analyticOnNhd_iff_differentiableOn {f : E → V} {U : Set E} (hU : IsOpen U) :
    AnalyticOnNhd ℂ f U ↔ DifferentiableOn ℂ f U := by sorry
