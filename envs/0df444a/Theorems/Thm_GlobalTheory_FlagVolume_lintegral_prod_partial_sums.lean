-- Prove2me | Theorems.Thm_GlobalTheory_FlagVolume_lintegral_prod_partial_sums
-- name    : GlobalTheory.FlagVolume.lintegral_prod_partial_sums
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:05:14.217435+00:00
-- url     : https://prove2.me/theorems/2e9fad55-eaff-51a5-ae68-ec57448d5458
-- title:
--   Flag Volume: lintegral prod partial sums
-- statement:
--   The Flag Volume construction uses the lintegral prod partial sums property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralProdPartialSums.lean#L94-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralProdPartialSums.lean#L94-L130

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralProdPartialSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real Set Filter Topology
open scoped ENNReal Nat
open GlobalTheory GlobalTheory.FlagVolume

theorem GlobalTheory.FlagVolume.lintegral_prod_partial_sums (n : ℕ) : ∀ {A : ℝ}, 0 < A →
    ∫⁻ z : Fin n → ℂ, ENNReal.ofReal
      (∏ i : Fin n, ((A + ∑ k, if k ≤ i then ‖z k‖ ^ 2 else 0) ^ 2)⁻¹) =
      ENNReal.ofReal (π ^ n / n ! * (A ^ n)⁻¹) := by sorry
