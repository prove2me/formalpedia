-- Prove2me | Theorems.Thm_GlobalTheory_SCV_tendstoUniformlyOn_fderiv_ball
-- name    : GlobalTheory.SCV.tendstoUniformlyOn_fderiv_ball
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:48.918191+00:00
-- url     : https://prove2.me/theorems/03067917-033b-416a-9ffb-055627a0374a
-- title:
--   SCV: tendsto Uniformly On fderiv ball
-- statement:
--   The SCV construction uses the tendsto Uniformly On fderiv ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L50-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L50-L91

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
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem GlobalTheory.SCV.tendstoUniformlyOn_fderiv_ball [CompleteSpace V] {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → E → V} {f : E → V} {c : E} {r : ℝ}
    (hlim : TendstoUniformlyOn F f l (ball c (2 * r)))
    (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) (ball c (2 * r))) :
    DifferentiableOn ℂ f (ball c r) ∧
      TendstoUniformlyOn (fun n => fderiv ℂ (F n)) (fderiv ℂ f) l (ball c r) := by sorry
