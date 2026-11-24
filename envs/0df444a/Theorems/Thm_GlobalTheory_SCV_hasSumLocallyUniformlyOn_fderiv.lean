-- Prove2me | Theorems.Thm_GlobalTheory_SCV_hasSumLocallyUniformlyOn_fderiv
-- name    : GlobalTheory.SCV.hasSumLocallyUniformlyOn_fderiv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:36.672808+00:00
-- url     : https://prove2.me/theorems/7f38ea98-910d-4e25-a9ba-d644ec4af1c6
-- title:
--   SCV: has Sum Locally Uniformly On fderiv
-- statement:
--   The SCV construction uses the has Sum Locally Uniformly On fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L393-L400
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L393-L400

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

theorem GlobalTheory.SCV.hasSumLocallyUniformlyOn_fderiv (hU : IsOpen U)
    (hsum : HasSumLocallyUniformlyOn F f U) (hF : ∀ i, DifferentiableOn ℂ (F i) U) :
    HasSumLocallyUniformlyOn (fun i => fderiv ℂ (F i)) (fderiv ℂ f) U := by sorry
