-- Prove2me | Theorems.Thm_GlobalTheory_IntBall_colGram_three_unitLower
-- name    : GlobalTheory.IntBall.colGram_three_unitLower
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:45:35.200087+00:00
-- url     : https://prove2.me/theorems/3c06c3db-e911-474a-963b-9d7f61b83ee1
-- title:
--   Int Ball: col Gram three unit Lower
-- statement:
--   The Int Ball construction uses the col Gram three unit Lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColumnGramDeterminantUnitLowerThree.lean#L8-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColumnGramDeterminantUnitLowerThree.lean#L8-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColumnGramDeterminantUnitLowerThree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
open GlobalTheory GlobalTheory.IntBall

theorem GlobalTheory.IntBall.colGram_three_unitLower : ∀ M : Matrix (Fin 3) (Fin 3) ℂ, (∀ i, M i i = 1) →
    (∀ i j : Fin 3, i < j → M i j = 0) →
    colGram M 1 = 1 + ‖M 1 0‖ ^ 2 + ‖M 2 0‖ ^ 2 ∧
      colGram M 2 = 1 + ‖M 2 1‖ ^ 2 + ‖M 1 0 * M 2 1 - M 2 0‖ ^ 2 := by sorry
