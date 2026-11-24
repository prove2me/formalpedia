-- Prove2me | Theorems.Thm_GlobalTheory_SCV_hasSum_iteratedFDeriv_of_locally_normal
-- name    : GlobalTheory.SCV.hasSum_iteratedFDeriv_of_locally_normal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:08.970616+00:00
-- url     : https://prove2.me/theorems/a4213a19-b657-43e3-8625-62097f3e569a
-- title:
--   SCV: has Sum iterated FDeriv of locally normal
-- statement:
--   The SCV construction uses the has Sum iterated FDeriv of locally normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L436-L442
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L436-L442

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

theorem GlobalTheory.SCV.hasSum_iteratedFDeriv_of_locally_normal (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hle : ∀ x ∈ U, ∃ t ∈ 𝓝 x, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ z ∈ t, ‖F i z‖ ≤ u i)
    (k : ℕ) {z : E} (hz : z ∈ U) :
    HasSum (fun i => iteratedFDeriv ℂ k (F i) z) (iteratedFDeriv ℂ k (fun w => ∑' i, F i w) z) := by sorry
