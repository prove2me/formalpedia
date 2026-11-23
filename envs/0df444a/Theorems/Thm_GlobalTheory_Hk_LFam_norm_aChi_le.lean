-- Prove2me | Theorems.Thm_GlobalTheory_Hk_LFam_norm_aChi_le
-- name    : GlobalTheory.Hk.LFam.norm_aChi_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:44.659063+00:00
-- url     : https://prove2.me/theorems/70a0783c-566a-4365-8049-80465a8ffa3f
-- title:
--   LFam: norm a Chi le
-- statement:
--   The LFam construction uses the norm a Chi le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExpSumBounds.lean#L150-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExpSumBounds.lean#L150-L158

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

theorem GlobalTheory.Hk.LFam.norm_aChi_le (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (n : ℕ) : ‖𝓕.aChi χ n‖ ≤ 14 * 𝓕.B * n := by sorry
