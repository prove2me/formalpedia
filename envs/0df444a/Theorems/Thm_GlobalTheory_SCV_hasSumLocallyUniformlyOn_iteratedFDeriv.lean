-- Prove2me | Theorems.Thm_GlobalTheory_SCV_hasSumLocallyUniformlyOn_iteratedFDeriv
-- name    : GlobalTheory.SCV.hasSumLocallyUniformlyOn_iteratedFDeriv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:53.22+00:00
-- url     : https://prove2.me/theorems/7ca19341-1ce1-47c4-a20e-37e9d386acec
-- title:
--   SCV: has Sum Locally Uniformly On iterated FDeriv
-- statement:
--   The SCV construction uses the has Sum Locally Uniformly On iterated FDeriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L402-L410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L402-L410

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

theorem GlobalTheory.SCV.hasSumLocallyUniformlyOn_iteratedFDeriv (hU : IsOpen U)
    (hsum : HasSumLocallyUniformlyOn F f U) (hF : ∀ i, DifferentiableOn ℂ (F i) U) (k : ℕ) :
    HasSumLocallyUniformlyOn (fun i => iteratedFDeriv ℂ k (F i)) (iteratedFDeriv ℂ k f) U := by sorry
