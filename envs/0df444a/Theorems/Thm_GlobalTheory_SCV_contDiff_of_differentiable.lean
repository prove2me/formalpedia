-- Prove2me | Theorems.Thm_GlobalTheory_SCV_contDiff_of_differentiable
-- name    : GlobalTheory.SCV.contDiff_of_differentiable
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:13.964535+00:00
-- url     : https://prove2.me/theorems/0dbf6c31-f2ea-4e1d-b8dc-6707f47de3ed
-- title:
--   SCV: cont Diff of differentiable
-- statement:
--   The SCV construction uses the cont Diff of differentiable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L317-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L317-L319

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

theorem GlobalTheory.SCV.contDiff_of_differentiable {f : E → V} (hf : Differentiable ℂ f) (n : WithTop ℕ∞) :
    ContDiff ℂ n f := by sorry
