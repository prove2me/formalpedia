-- Prove2me | Theorems.Thm_GlobalTheory_IntBall_colGram_blkW_last
-- name    : GlobalTheory.IntBall.colGram_blkW_last
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:44:55.72991+00:00
-- url     : https://prove2.me/theorems/ff3b2b85-d59f-537b-944f-5a1186a6556b
-- title:
--   Int Ball: col Gram blk W last
-- statement:
--   The Int Ball construction uses the col Gram blk W last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColumnGramDeterminantUnitLowerBlockLastEqOne.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColumnGramDeterminantUnitLowerBlockLastEqOne.lean#L21-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColumnGramDeterminantUnitLowerBlockLastEqOne
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

theorem GlobalTheory.IntBall.colGram_blkW_last (r p0 : ℕ) (w : Low r → ℂ) :
    colGram (blkW p0 w) (Fin.last (r - 1)) = 1 := by sorry
