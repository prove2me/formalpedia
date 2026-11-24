-- Prove2me | Theorems.Thm_GlobalTheory_SummableExpNegAbsSum_summable_int
-- name    : GlobalTheory.SummableExpNegAbsSum.summable_int
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:23:19.665826+00:00
-- url     : https://prove2.me/theorems/53c127a4-c37e-4551-8ca7-e95c793f412b
-- title:
--   Summable Exp Neg Abs Sum: summable int
-- statement:
--   The Summable Exp Neg Abs Sum construction uses the summable int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/SummableExpNegSumAbs.lean#L5-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/SummableExpNegSumAbs.lean#L5-L9

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

theorem GlobalTheory.SummableExpNegAbsSum.summable_int : Summable fun n : ℤ ↦ Real.exp (-|(n : ℝ)|) := by sorry
