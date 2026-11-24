-- Prove2me | Theorems.Thm_GlobalTheory_SCV_fderiv_eq_zero_of_real_lines
-- name    : GlobalTheory.SCV.fderiv_eq_zero_of_real_lines
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:31:53.170799+00:00
-- url     : https://prove2.me/theorems/ad0183a6-851d-4a0e-896a-345ae343b2e6
-- title:
--   SCV: fderiv eq zero of real lines
-- statement:
--   The SCV construction uses the fderiv eq zero of real lines property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EventuallyIteratedFDerivEqZeroOfRealSubspace.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EventuallyIteratedFDerivEqZeroOfRealSubspace.lean#L31-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EventuallyIteratedFDerivEqZeroOfRealSubspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem GlobalTheory.SCV.fderiv_eq_zero_of_real_lines {f : E → V} {x : E} {S : Set E}
    (hS : Submodule.span ℂ S = ⊤) (hf : DifferentiableAt ℂ f x)
    (h : ∀ s ∈ S, ∀ᶠ t : ℝ in 𝓝 0, f (x + (t : ℂ) • s) = f x) : fderiv ℂ f x = 0 := by sorry
