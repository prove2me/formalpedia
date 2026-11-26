-- Prove2me | Theorems.Thm_GlobalTheory_abs_factorial_mul_eval_sub_top_le
-- name    : GlobalTheory.abs_factorial_mul_eval_sub_top_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:43:42.347507+00:00
-- url     : https://prove2.me/theorems/95fb3e18-e137-5aae-8b31-0cc17ba2b992
-- title:
--   Global Theory: abs factorial mul eval sub top le
-- statement:
--   The Global Theory construction uses the abs factorial mul eval sub top le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsFactorialMulEvalSubTopLe.lean#L5-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsFactorialMulEvalSubTopLe.lean#L5-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsFactorialMulEvalSubTopLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.abs_factorial_mul_eval_sub_top_le (d : ℕ) (p : Polynomial ℚ) (hp : p.natDegree ≤ d) :
    ∃ C : ℕ, ∀ m : ℕ, |(d.factorial : ℚ) * p.eval (m : ℚ) - (d.factorial : ℚ) * p.coeff d * (m : ℚ) ^ d|
      ≤ C * ((d : ℚ) * ((m : ℚ) + 1) ^ (d - 1)) := by sorry
