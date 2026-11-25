-- Prove2me | Theorems.Thm_GlobalTheory_T_sum_mul_nonneg_and_pos_of_posDef_of_posSemidef
-- name    : GlobalTheory.T.sum_mul_nonneg_and_pos_of_posDef_of_posSemidef
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:38:56.048199+00:00
-- url     : https://prove2.me/theorems/7556bfa0-392b-5b6a-82dd-0a90181021ea
-- title:
--   T: sum mul nonneg and pos of pos Def of pos Semidef
-- statement:
--   The T construction uses the sum mul nonneg and pos of pos Def of pos Semidef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumHadamardPosDefPosSemidefStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumHadamardPosDefPosSemidefStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumHadamardPosDefPosSemidef
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumHadamardPosDefPosSemidefStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.sum_mul_nonneg_and_pos_of_posDef_of_posSemidef : ∀ {r : ℕ} (S G : Matrix (Fin r) (Fin r) ℝ), S.PosDef → G.PosSemidef → 0 ≤ ∑ i, ∑ j, S i j * G i j ∧ (G ≠ 0 → 0 < ∑ i, ∑ j, S i j * G i j) := by sorry
