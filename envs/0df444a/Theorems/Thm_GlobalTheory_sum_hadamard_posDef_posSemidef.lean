-- Prove2me | Theorems.Thm_GlobalTheory_sum_hadamard_posDef_posSemidef
-- name    : GlobalTheory.sum_hadamard_posDef_posSemidef
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:22:37.052806+00:00
-- url     : https://prove2.me/theorems/817e617f-1c76-4a84-9182-592dac852ea4
-- title:
--   Global Theory: sum hadamard pos Def pos Semidef
-- statement:
--   The Global Theory construction uses the sum hadamard pos Def pos Semidef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumHadamardPosDefPosSemidef.lean#L7-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumHadamardPosDefPosSemidef.lean#L7-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumHadamardPosDefPosSemidef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix

theorem GlobalTheory.sum_hadamard_posDef_posSemidef :
    ∀ {r : ℕ} (S G : Matrix (Fin r) (Fin r) ℝ), S.PosDef → G.PosSemidef →
      0 ≤ ∑ i, ∑ j, S i j * G i j ∧ (G ≠ 0 → 0 < ∑ i, ∑ j, S i j * G i j) := by sorry
