-- Prove2me | Theorems.Thm_GlobalTheory_exp_neg_mul_sqrt_div_pow_le
-- name    : GlobalTheory.exp_neg_mul_sqrt_div_pow_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:45:55.160522+00:00
-- url     : https://prove2.me/theorems/40082c16-9b3a-42ea-a248-786faaf2deac
-- title:
--   Global Theory: exp neg mul sqrt div pow le
-- statement:
--   The Global Theory construction uses the exp neg mul sqrt div pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExpNegMulSqrtDivPowLe.lean#L5-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExpNegMulSqrtDivPowLe.lean#L5-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExpNegMulSqrtDivPowLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exp_neg_mul_sqrt_div_pow_le (a : ℝ) (D : ℕ) (ha : 0 < a) :
    ∃ C : ℝ, ∀ m : ℕ, Real.exp (-(a * m * ((m : ℝ) + 1) ^ (-(1 / 2 : ℝ)))) /
      (((m : ℝ) + 1) ^ (-(1 / 2 : ℝ))) ^ D ≤ C * Real.sqrt (((m : ℝ) + 1) ^ (-(1 / 2 : ℝ))) := by sorry
