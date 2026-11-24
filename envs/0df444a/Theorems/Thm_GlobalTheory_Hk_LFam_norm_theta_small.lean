-- Prove2me | Theorems.Thm_GlobalTheory_Hk_LFam_norm_theta_small
-- name    : GlobalTheory.Hk.LFam.norm_theta_small
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:21:33.438837+00:00
-- url     : https://prove2.me/theorems/c79a83dc-19e5-49f2-8278-012b88c869f2
-- title:
--   LFam: norm theta small
-- statement:
--   The LFam construction uses the norm theta small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExpSumBounds.lean#L196-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExpSumBounds.lean#L196-L223

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

theorem GlobalTheory.Hk.LFam.norm_theta_small (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ‖∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) - 𝓕.res χ / t‖ ≤ 𝓕.B ^ 11 * t := by sorry
