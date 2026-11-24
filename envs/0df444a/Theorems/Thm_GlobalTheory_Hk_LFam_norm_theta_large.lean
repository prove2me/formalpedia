-- Prove2me | Theorems.Thm_GlobalTheory_Hk_LFam_norm_theta_large
-- name    : GlobalTheory.Hk.LFam.norm_theta_large
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:21:30.143533+00:00
-- url     : https://prove2.me/theorems/8688a9b3-5037-46e7-93f9-00b4fa80b020
-- title:
--   LFam: norm theta large
-- statement:
--   The LFam construction uses the norm theta large property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExpSumBounds.lean#L175-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExpSumBounds.lean#L175-L194

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk

theorem GlobalTheory.Hk.LFam.norm_theta_large (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {t : ℝ} (ht : 1 ≤ t) :
    ‖∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ)‖ ≤
      (14 * ∑' n : ℕ, (n : ℝ) * Real.exp (-(1 / 2 * n))) * 𝓕.B * Real.exp (-(t / 2)) := by sorry
