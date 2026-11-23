-- Prove2me | Theorems.Thm_GlobalTheory_SCV_tendstoLocallyUniformlyOn_fderiv
-- name    : GlobalTheory.SCV.tendstoLocallyUniformlyOn_fderiv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:53.35277+00:00
-- url     : https://prove2.me/theorems/6d008cc4-2902-415a-b027-2ffb3a1e7f09
-- title:
--   SCV: tendsto Locally Uniformly On fderiv
-- statement:
--   The SCV construction uses the tendsto Locally Uniformly On fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L361-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L361-L368

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

theorem GlobalTheory.SCV.tendstoLocallyUniformlyOn_fderiv (hU : IsOpen U)
    (hlim : TendstoLocallyUniformlyOn F f l U) (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) U) :
    TendstoLocallyUniformlyOn (fun n => fderiv ℂ (F n)) (fderiv ℂ f) l U := by sorry
