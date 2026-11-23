-- Prove2me | Theorems.Thm_GlobalTheory_SCV_hasSumLocallyUniformlyOn_of_locally_normal
-- name    : GlobalTheory.SCV.hasSumLocallyUniformlyOn_of_locally_normal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:46.915657+00:00
-- url     : https://prove2.me/theorems/3eb6ba9a-f758-4420-8603-b1b61f1fc593
-- title:
--   SCV: has Sum Locally Uniformly On of locally normal
-- statement:
--   The SCV construction uses the has Sum Locally Uniformly On of locally normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L414-L420
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L414-L420

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
omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedSpace ℂ V]

theorem GlobalTheory.SCV.hasSumLocallyUniformlyOn_of_locally_normal
    (hle : ∀ x ∈ U, ∃ t ∈ 𝓝 x, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ z ∈ t, ‖F i z‖ ≤ u i) :
    HasSumLocallyUniformlyOn F (fun z => ∑' i, F i z) U := by sorry
