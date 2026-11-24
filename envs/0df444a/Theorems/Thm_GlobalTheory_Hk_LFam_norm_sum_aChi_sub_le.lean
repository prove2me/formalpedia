-- Prove2me | Theorems.Thm_GlobalTheory_Hk_LFam_norm_sum_aChi_sub_le
-- name    : GlobalTheory.Hk.LFam.norm_sum_aChi_sub_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:21:21.348854+00:00
-- url     : https://prove2.me/theorems/755fc796-fc2d-420a-92a3-ff35e66840a9
-- title:
--   LFam: norm sum a Chi sub le
-- statement:
--   The LFam construction uses the norm sum a Chi sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExpSumBounds.lean#L225-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExpSumBounds.lean#L225-L236

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

theorem GlobalTheory.Hk.LFam.norm_sum_aChi_sub_le (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {x : ℝ} (hx : 1 ≤ x) :
    ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, 𝓕.aChi χ n - 𝓕.res χ * x‖ ≤ 10 * 𝓕.B * Real.sqrt x := by sorry
