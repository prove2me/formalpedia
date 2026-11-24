-- Prove2me | Theorems.Thm_GlobalTheory_SCV_contDiffAt_of_differentiableOn
-- name    : GlobalTheory.SCV.contDiffAt_of_differentiableOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:48.523812+00:00
-- url     : https://prove2.me/theorems/6ce5fdad-0769-4006-ae91-ec3fa23ff372
-- title:
--   SCV: cont Diff At of differentiable On
-- statement:
--   The SCV construction uses the cont Diff At of differentiable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L313-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L313-L315

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

theorem GlobalTheory.SCV.contDiffAt_of_differentiableOn {f : E → V} {s : Set E} {c : E}
    (hf : DifferentiableOn ℂ f s) (hs : s ∈ 𝓝 c) (n : WithTop ℕ∞) : ContDiffAt ℂ n f c := by sorry
