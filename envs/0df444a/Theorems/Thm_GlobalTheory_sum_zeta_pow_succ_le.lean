-- Prove2me | Theorems.Thm_GlobalTheory_sum_zeta_pow_succ_le
-- name    : GlobalTheory.sum_zeta_pow_succ_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:22:22.255819+00:00
-- url     : https://prove2.me/theorems/4be95ced-4c9f-40af-9197-70676ed7013d
-- title:
--   Global Theory: sum zeta pow succ le
-- statement:
--   The Global Theory construction uses the sum zeta pow succ le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIdealInClassOfNormLeSqrtDiscr.lean#L8-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIdealInClassOfNormLeSqrtDiscr.lean#L8-L36

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

theorem GlobalTheory.sum_zeta_pow_succ_le (k : ℕ) {X : ℝ} (hX : 1 ≤ X) (N : ℕ) (hN : (N : ℝ) ≤ X) :
    ((∑ n ∈ Ioc 0 N, (ζ ^ (k + 1) : ArithmeticFunction ℕ) n : ℕ) : ℝ)
      ≤ N * (1 + Real.log X) ^ k := by sorry
