-- Prove2me | Theorems.Thm_GlobalTheory_StrictUpperNilpotentFlagMeasures_pow_apply_eq_zero_of_strictUpper
-- name    : GlobalTheory.StrictUpperNilpotentFlagMeasures.pow_apply_eq_zero_of_strictUpper
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:34:07.607378+00:00
-- url     : https://prove2.me/theorems/12006c26-7ba7-5b6d-b1a3-e41934af0ad8
-- title:
--   Strict Upper Nilpotent Flag Measures: pow apply eq zero of strict Upper
-- statement:
--   The Strict Upper Nilpotent Flag Measures construction uses the pow apply eq zero of strict Upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PowApplyEqZeroOfStrictUpper.lean#L5-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PowApplyEqZeroOfStrictUpper.lean#L5-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PowApplyEqZeroOfStrictUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.StrictUpperNilpotentFlagMeasures

theorem GlobalTheory.StrictUpperNilpotentFlagMeasures.pow_apply_eq_zero_of_strictUpper {m : ℕ} {X : Matrix (Fin m) (Fin m) ℂ}
    (hX : ∀ i j : Fin m, (j : ℕ) ≤ (i : ℕ) → X i j = 0) (n : ℕ) :
    ∀ i j : Fin m, (j : ℕ) < (i : ℕ) + n → (X ^ n) i j = 0 := by sorry
