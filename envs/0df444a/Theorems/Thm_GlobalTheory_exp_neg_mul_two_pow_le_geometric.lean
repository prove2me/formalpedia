-- Prove2me | Theorems.Thm_GlobalTheory_exp_neg_mul_two_pow_le_geometric
-- name    : GlobalTheory.exp_neg_mul_two_pow_le_geometric
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:33:39.891933+00:00
-- url     : https://prove2.me/theorems/c0d43fda-ec89-498a-994f-57610d625429
-- title:
--   Global Theory: exp neg mul two pow le geometric
-- statement:
--   The Global Theory construction uses the exp neg mul two pow le geometric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ShellSumElementaryInequalities.lean#L7-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ShellSumElementaryInequalities.lean#L7-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ShellSumElementaryInequalities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Real
open GlobalTheory

theorem GlobalTheory.exp_neg_mul_two_pow_le_geometric (T : ℝ) (hT : 1 ≤ T) (i : ℕ) :
    Real.exp (-T * 2 ^ i) ≤ Real.exp (-T) * (1 / 2 : ℝ) ^ i := by sorry
