-- Prove2me | Theorems.Thm_GlobalTheory_SCV_analyticAt_iff_eventually_differentiableAt
-- name    : GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:09:00.783147+00:00
-- url     : https://prove2.me/theorems/94c3cac8-3131-45e4-ac5d-815b6ed328be
-- title:
--   SCV: analytic At iff eventually differentiable At
-- statement:
--   The SCV construction uses the analytic At iff eventually differentiable At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L299-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L299-L303

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

theorem GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt {f : E → V} {c : E} :
    AnalyticAt ℂ f c ↔ ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f z := by sorry
