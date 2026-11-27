-- Prove2me | Theorems.Thm_GlobalTheory_sum_bound_of_step_diff
-- name    : GlobalTheory.sum_bound_of_step_diff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:50:57.168508+00:00
-- url     : https://prove2.me/theorems/1757e0c4-4f5a-41d8-b232-a7cea32ab115
-- title:
--   Global Theory: sum bound of step diff
-- statement:
--   The Global Theory construction uses the sum bound of step diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumBoundOfStepDiff.lean#L5-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumBoundOfStepDiff.lean#L5-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumBoundOfStepDiff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.sum_bound_of_step_diff :
    ∀ (a : ℕ → ℕ) (d p C : ℕ), 1 ≤ p →
      (∀ m : ℕ, a (m + p) ≤ a m + C * (d * (m + p + 1) ^ (d - 1))) →
      ∃ C' : ℕ, ∀ m : ℕ, a m ≤ C' * ((d + 1) * (m + 1) ^ d) := by sorry
