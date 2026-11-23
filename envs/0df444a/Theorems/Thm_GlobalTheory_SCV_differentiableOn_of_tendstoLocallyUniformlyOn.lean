-- Prove2me | Theorems.Thm_GlobalTheory_SCV_differentiableOn_of_tendstoLocallyUniformlyOn
-- name    : GlobalTheory.SCV.differentiableOn_of_tendstoLocallyUniformlyOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:23.998192+00:00
-- url     : https://prove2.me/theorems/ab0b55d8-015a-40fd-b79e-7a12bb18ed5a
-- title:
--   SCV: differentiable On of tendsto Locally Uniformly On
-- statement:
--   The SCV construction uses the differentiable On of tendsto Locally Uniformly On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L354-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L354-L359

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
variable {ι : Type*} {l : Filter ι} {F : ι → E → V} {f : E → V} {U : Set E}

theorem GlobalTheory.SCV.differentiableOn_of_tendstoLocallyUniformlyOn [l.NeBot] (hU : IsOpen U)
    (hlim : TendstoLocallyUniformlyOn F f l U) (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) U) :
    DifferentiableOn ℂ f U := by sorry
