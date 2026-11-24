-- Prove2me | Theorems.Thm_GlobalTheory_two_pow_mul_factorial_succ_le
-- name    : GlobalTheory.two_pow_mul_factorial_succ_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:24:21.947243+00:00
-- url     : https://prove2.me/theorems/2703ed05-0298-4368-931d-a475241611ce
-- title:
--   Global Theory: two pow mul factorial succ le
-- statement:
--   The Global Theory construction uses the two pow mul factorial succ le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIdealInClassOfNormLeSqrtDiscr.lean#L211-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIdealInClassOfNormLeSqrtDiscr.lean#L211-L231

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Real NumberField ArithmeticFunction.zeta
open Module NumberField Finset
open GlobalTheory
variable (K : Type*) [Field K] [NumberField K]

theorem GlobalTheory.two_pow_mul_factorial_succ_le (n : ℕ) :
    (2 : ℝ) ^ n * ((n + 1).factorial : ℝ) ≤ ((n : ℝ) + 1) ^ (n + 1) := by sorry
