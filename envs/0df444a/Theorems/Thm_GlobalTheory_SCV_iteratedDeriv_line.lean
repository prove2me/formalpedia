-- Prove2me | Theorems.Thm_GlobalTheory_SCV_iteratedDeriv_line
-- name    : GlobalTheory.SCV.iteratedDeriv_line
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:33:14.792824+00:00
-- url     : https://prove2.me/theorems/234d8ea9-0394-4f23-a20d-d67ecc43358b
-- title:
--   SCV: iterated Deriv line
-- statement:
--   The SCV construction uses the iterated Deriv line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L217-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L217-L235

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

theorem GlobalTheory.SCV.iteratedDeriv_line {f : E → V} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {c : E} (hc : c ∈ U) (y : E) (n : ℕ) :
    iteratedDeriv n (fun t : ℂ => f (c + t • y)) 0 = iteratedFDeriv ℂ n f c (fun _ => y) := by sorry
