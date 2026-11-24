-- Prove2me | Theorems.Thm_GlobalTheory_sum_zeta_pow_le
-- name    : GlobalTheory.sum_zeta_pow_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:22:27.040112+00:00
-- url     : https://prove2.me/theorems/e6bf1ebd-9685-4d23-8741-a4532b23075f
-- title:
--   Global Theory: sum zeta pow le
-- statement:
--   The Global Theory construction uses the sum zeta pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIdealInClassOfNormLeSqrtDiscr.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIdealInClassOfNormLeSqrtDiscr.lean#L38-L46

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

theorem GlobalTheory.sum_zeta_pow_le {k : ℕ} (hk : 1 ≤ k) {X : ℝ} (hX : 1 ≤ X) :
    ((∑ n ∈ Ioc 0 ⌊X⌋₊, (ζ ^ k : ArithmeticFunction ℕ) n : ℕ) : ℝ)
      ≤ X * (1 + Real.log X) ^ (k - 1) := by sorry
