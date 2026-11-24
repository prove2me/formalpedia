-- Prove2me | Theorems.Thm_GlobalTheory_SCV_norm_iteratedFDeriv_le_pow
-- name    : GlobalTheory.SCV.norm_iteratedFDeriv_le_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:32:58.756262+00:00
-- url     : https://prove2.me/theorems/3702f89d-f19d-4ccd-ba04-302bd7341c4d
-- title:
--   SCV: norm iterated FDeriv le pow
-- statement:
--   The SCV construction uses the norm iterated FDeriv le pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L172-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L172-L192

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

theorem GlobalTheory.SCV.norm_iteratedFDeriv_le_pow {f : E → V} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {δ M : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∀ x : E, closedBall x (n * δ) ⊆ U → (∀ z ∈ closedBall x (n * δ), ‖f z‖ ≤ M) →
      ‖iteratedFDeriv ℂ n f x‖ ≤ M * (2 / δ) ^ n := by sorry
