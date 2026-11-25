-- Prove2me | Theorems.Thm_GlobalTheory_IntBall_ColGramPos_blkW_diag
-- name    : GlobalTheory.IntBall.ColGramPos.blkW_diag
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:45:34.214429+00:00
-- url     : https://prove2.me/theorems/05c8c616-5bca-43e1-a2a4-e977625ff672
-- title:
--   Col Gram Pos: blk W diag
-- statement:
--   The Col Gram Pos construction uses the blk W diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColumnGramDeterminantDiagonalBlockUnitLowerPos.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColumnGramDeterminantDiagonalBlockUnitLowerPos.lean#L20-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColumnGramDeterminantDiagonalBlockUnitLowerPos
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
open GlobalTheory GlobalTheory.IntBall GlobalTheory.IntBall.ColGramPos
open scoped ComplexOrder

theorem GlobalTheory.IntBall.ColGramPos.blkW_diag {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) (i : Fin (r - 1)) :
    blkW p0 w i i = 1 := by sorry
