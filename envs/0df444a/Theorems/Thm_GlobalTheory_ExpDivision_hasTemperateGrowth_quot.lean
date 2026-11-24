-- Prove2me | Theorems.Thm_GlobalTheory_ExpDivision_hasTemperateGrowth_quot
-- name    : GlobalTheory.ExpDivision.hasTemperateGrowth_quot
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:06:57.711716+00:00
-- url     : https://prove2.me/theorems/9e6d6ffc-72e2-461f-ac65-b8c18cf04c85
-- title:
--   Exp Division: has Temperate Growth quot
-- statement:
--   The Exp Division construction uses the has Temperate Growth quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityAsSumExpMinusOne.lean#L102-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityAsSumExpMinusOne.lean#L102-L121

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.ExpDivision

theorem GlobalTheory.ExpDivision.hasTemperateGrowth_quot (a : ℝ) : (fun t : ℝ => quot a t).HasTemperateGrowth := by sorry
