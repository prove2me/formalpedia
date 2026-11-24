-- Prove2me | Theorems.Thm_GlobalTheory_CharFormDeriv_norm_cexp_mul_I_sub_one_sub_le
-- name    : GlobalTheory.CharFormDeriv.norm_cexp_mul_I_sub_one_sub_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:17.142883+00:00
-- url     : https://prove2.me/theorems/cfe4ca8d-10fa-49bb-903b-f87b31fcd073
-- title:
--   Char Form Deriv: norm cexp mul I sub one sub le
-- statement:
--   The Char Form Deriv construction uses the norm cexp mul I sub one sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivRemCompLe.lean#L45-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivRemCompLe.lean#L45-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open GlobalTheory GlobalTheory.CharFormDeriv

theorem GlobalTheory.CharFormDeriv.norm_cexp_mul_I_sub_one_sub_le (z : ℝ) :
    ‖Complex.exp (z * I) - 1 - z * I‖ ≤ 3 * z ^ 2 := by sorry
