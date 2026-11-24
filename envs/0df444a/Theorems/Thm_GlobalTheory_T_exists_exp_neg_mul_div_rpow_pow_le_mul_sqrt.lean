-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_exp_neg_mul_div_rpow_pow_le_mul_sqrt
-- name    : GlobalTheory.T.exists_exp_neg_mul_div_rpow_pow_le_mul_sqrt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:36:05.778612+00:00
-- url     : https://prove2.me/theorems/4434a982-f853-41f4-8c7e-6cd4cb88506d
-- title:
--   T: exists exp neg mul div rpow pow le mul sqrt
-- statement:
--   The T construction uses the exists exp neg mul div rpow pow le mul sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExpNegMulSqrtDivPowLeStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExpNegMulSqrtDivPowLeStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExpNegMulSqrtDivPowLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExpNegMulSqrtDivPowLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_exp_neg_mul_div_rpow_pow_le_mul_sqrt : ∀ (a : ℝ) (D : ℕ), 0 < a → ∃ C : ℝ, ∀ m : ℕ, Real.exp (-(a * m * ((m : ℝ) + 1) ^ (-(1 / 2 : ℝ)))) / (((m : ℝ) + 1) ^ (-(1 / 2 : ℝ))) ^ D ≤ C * Real.sqrt (((m : ℝ) + 1) ^ (-(1 / 2 : ℝ))) := by sorry
