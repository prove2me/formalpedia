-- Prove2me | Theorems.Thm_GlobalTheory_SummableExpNegAbsSum_summable_exp_neg_sum_abs
-- name    : GlobalTheory.SummableExpNegAbsSum.summable_exp_neg_sum_abs
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:23:37.787005+00:00
-- url     : https://prove2.me/theorems/e880d7a7-a969-4257-a2f3-b2c5a108fba4
-- title:
--   Summable Exp Neg Abs Sum: summable exp neg sum abs
-- statement:
--   The Summable Exp Neg Abs Sum construction uses the summable exp neg sum abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/SummableExpNegSumAbs.lean#L11-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/SummableExpNegSumAbs.lean#L11-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SummableExpNegAbsSum

theorem GlobalTheory.SummableExpNegAbsSum.summable_exp_neg_sum_abs {ι : Type} [inst : Fintype ι] :
    Summable fun (m : ι → ℤ) ↦ Real.exp (-∑ i : ι, |(↑(m i) : ℝ)|) := by sorry
