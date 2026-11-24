-- Prove2me | Theorems.Thm_GlobalTheory_SCV_norm_iteratedFDeriv_le_factorial
-- name    : GlobalTheory.SCV.norm_iteratedFDeriv_le_factorial
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:33:25.317608+00:00
-- url     : https://prove2.me/theorems/261b26b7-2bde-4be6-9a0d-afe2af5c0980
-- title:
--   SCV: norm iterated FDeriv le factorial
-- statement:
--   The SCV construction uses the norm iterated FDeriv le factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L194-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L194-L215

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

theorem GlobalTheory.SCV.norm_iteratedFDeriv_le_factorial {f : E → V} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {c : E} {R M : ℝ} (hR : 0 < R) (hc : closedBall c R ⊆ U)
    (hM : ∀ z ∈ closedBall c R, ‖f z‖ ≤ M) (n : ℕ) :
    ‖iteratedFDeriv ℂ n f c‖ ≤ n ! * (M * (2 * Real.exp 1 / R) ^ n) := by sorry
