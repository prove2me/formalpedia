-- Prove2me | Theorems.Thm_GlobalTheory_abs_log_inv_one_sub_le_two_mul_abs
-- name    : GlobalTheory.abs_log_inv_one_sub_le_two_mul_abs
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:26:51.451528+00:00
-- url     : https://prove2.me/theorems/26045252-ae5d-4d37-aee9-7443f895ab67
-- title:
--   Global Theory: abs log inv one sub le two mul abs
-- statement:
--   The Global Theory construction uses the abs log inv one sub le two mul abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsLogInvOneSubLeTwoMulAbs.lean#L7-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsLogInvOneSubLeTwoMulAbs.lean#L7-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsLogInvOneSubLeTwoMulAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory IsDedekindDomain NumberField
open GlobalTheory

theorem GlobalTheory.abs_log_inv_one_sub_le_two_mul_abs (y : ℝ) (hy : |y| ≤ 1 / 2) :
    |Real.log (1 - y)⁻¹| ≤ 2 * |y| := by sorry
