-- Prove2me | Theorems.Thm_GlobalTheory_SCV_hasFPowerSeriesAt_taylor
-- name    : GlobalTheory.SCV.hasFPowerSeriesAt_taylor
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:33:23.986106+00:00
-- url     : https://prove2.me/theorems/915d0a5a-7d7f-4c35-9383-0976f0c7d7dc
-- title:
--   SCV: has FPower Series At taylor
-- statement:
--   The SCV construction uses the has FPower Series At taylor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L256-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L256-L284

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

theorem GlobalTheory.SCV.hasFPowerSeriesAt_taylor {f : E → V} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {c : E} (hc : c ∈ U) :
    HasFPowerSeriesAt f (fun n => (n ! : ℂ)⁻¹ • iteratedFDeriv ℂ n f c) c := by sorry
