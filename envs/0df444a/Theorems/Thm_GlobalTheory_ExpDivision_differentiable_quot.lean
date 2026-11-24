-- Prove2me | Theorems.Thm_GlobalTheory_ExpDivision_differentiable_quot
-- name    : GlobalTheory.ExpDivision.differentiable_quot
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:07:17.094443+00:00
-- url     : https://prove2.me/theorems/b6520925-427c-448e-893d-e11fef27b505
-- title:
--   Exp Division: differentiable quot
-- statement:
--   The Exp Division construction uses the differentiable quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityAsSumExpMinusOne.lean#L98-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityAsSumExpMinusOne.lean#L98-L100

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

theorem GlobalTheory.ExpDivision.differentiable_quot (a : ℝ) : Differentiable ℂ (quot a) := by sorry
