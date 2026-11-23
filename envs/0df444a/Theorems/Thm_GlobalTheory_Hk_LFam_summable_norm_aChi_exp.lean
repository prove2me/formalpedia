-- Prove2me | Theorems.Thm_GlobalTheory_Hk_LFam_summable_norm_aChi_exp
-- name    : GlobalTheory.Hk.LFam.summable_norm_aChi_exp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:54.789165+00:00
-- url     : https://prove2.me/theorems/c41557a7-bc1f-4e9c-b9a1-ab31e812fe59
-- title:
--   LFam: summable norm a Chi exp
-- statement:
--   The LFam construction uses the summable norm a Chi exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExpSumBounds.lean#L167-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExpSumBounds.lean#L167-L173

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

theorem GlobalTheory.Hk.LFam.summable_norm_aChi_exp (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => ‖𝓕.aChi χ n‖ * Real.exp (-(t * n))) := by sorry
