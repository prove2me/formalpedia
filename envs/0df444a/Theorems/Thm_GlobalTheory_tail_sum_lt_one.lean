-- Prove2me | Theorems.Thm_GlobalTheory_tail_sum_lt_one
-- name    : GlobalTheory.tail_sum_lt_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:51:48.594214+00:00
-- url     : https://prove2.me/theorems/432352d9-e8df-561d-b614-83351574bb9a
-- title:
--   Global Theory: tail sum lt one
-- statement:
--   The Global Theory construction uses the tail sum lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TailSumLtOne.lean#L5-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TailSumLtOne.lean#L5-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TailSumLtOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.tail_sum_lt_one {ι : Type*} (idx : ι → ℕ) (ρ n : ℕ) (hn : 4 * ρ + 4 ≤ n) (h2 : ∀ i, 2 ≤ idx i)
    (hc : ∀ m, {i | idx i = m}.Finite ∧ {i | idx i = m}.ncard ≤ m ^ (2 * ρ)) (c : ι → ℂ) (hcb : ∀ i, ‖c i‖ ≤ (idx i : ℝ) ^ (-(n : ℝ) / 2)) :
    Summable (fun i => ‖c i‖) ∧ ∑' i, ‖c i‖ ≤ 0.65 := by sorry
