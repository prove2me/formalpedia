-- Prove2me | Theorems.Thm_GlobalTheory_rpow_neg_le_one_sub_log_add_sq
-- name    : GlobalTheory.rpow_neg_le_one_sub_log_add_sq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:20:30.848609+00:00
-- url     : https://prove2.me/theorems/cc7dca0b-fa19-4f99-9925-78c0586eb2da
-- title:
--   Global Theory: rpow neg le one sub log add sq
-- statement:
--   The Global Theory construction uses the rpow neg le one sub log add sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsRpowNegSumLeOfSumLog.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsRpowNegSumLeOfSumLog.lean#L7-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsRpowNegSumLeOfSumLog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory

theorem GlobalTheory.rpow_neg_le_one_sub_log_add_sq {ω δ t : ℝ} (hω : 1 ≤ ω) (hδ : 0 < δ)
    (hδL : δ * Real.log ω ≤ 1) (h1 : ω⁻¹ ≤ t) (h2 : t ≤ ω) :
    t ^ (-δ) ≤ 1 - δ * Real.log t + (δ * Real.log ω) ^ 2 := by sorry
