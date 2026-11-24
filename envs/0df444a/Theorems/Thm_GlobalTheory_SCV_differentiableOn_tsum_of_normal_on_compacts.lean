-- Prove2me | Theorems.Thm_GlobalTheory_SCV_differentiableOn_tsum_of_normal_on_compacts
-- name    : GlobalTheory.SCV.differentiableOn_tsum_of_normal_on_compacts
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:31:48.577031+00:00
-- url     : https://prove2.me/theorems/055eaaa9-eb9a-4191-bca4-234c54af8bf4
-- title:
--   SCV: differentiable On tsum of normal on compacts
-- statement:
--   The SCV construction uses the differentiable On tsum of normal on compacts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L444-L457
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L444-L457

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

theorem GlobalTheory.SCV.differentiableOn_tsum_of_normal_on_compacts (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hle : ∀ K ⊆ U, IsCompact K → ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ z ∈ K, ‖F i z‖ ≤ u i) :
    DifferentiableOn ℂ (fun z => ∑' i, F i z) U ∧
      ∀ k : ℕ, HasSumLocallyUniformlyOn (fun i => iteratedFDeriv ℂ k (F i))
        (iteratedFDeriv ℂ k (fun w => ∑' i, F i w)) U := by sorry
