-- Prove2me | Theorems.Thm_GlobalTheory_T_columnGramDeterminant_unitLower_three
-- name    : GlobalTheory.T.columnGramDeterminant_unitLower_three
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:55:22.618846+00:00
-- url     : https://prove2.me/theorems/38918ef7-53e5-4d76-b56d-757d465af467
-- title:
--   T: column Gram Determinant unit Lower three
-- statement:
--   The T construction uses the column Gram Determinant unit Lower three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColumnGramDeterminantUnitLowerThreeStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColumnGramDeterminantUnitLowerThreeStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColumnGramDeterminantUnitLowerThree
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColumnGramDeterminantUnitLowerThreeStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.columnGramDeterminant_unitLower_three : ∀ M : Matrix (Fin 3) (Fin 3) ℂ, (∀ i, M i i = 1) → (∀ i j : Fin 3, i < j → M i j = 0) → colGram M 1 = 1 + ‖M 1 0‖ ^ 2 + ‖M 2 0‖ ^ 2 ∧ colGram M 2 = 1 + ‖M 2 1‖ ^ 2 + ‖M 1 0 * M 2 1 - M 2 0‖ ^ 2 := by sorry
