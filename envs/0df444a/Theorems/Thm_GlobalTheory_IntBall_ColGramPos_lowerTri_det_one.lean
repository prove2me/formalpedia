-- Prove2me | Theorems.Thm_GlobalTheory_IntBall_ColGramPos_lowerTri_det_one
-- name    : GlobalTheory.IntBall.ColGramPos.lowerTri_det_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:45:49.591812+00:00
-- url     : https://prove2.me/theorems/bea24f7c-3fb6-4555-a365-cf31820429b4
-- title:
--   Col Gram Pos: lower Tri det one
-- statement:
--   The Col Gram Pos construction uses the lower Tri det one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColumnGramDeterminantDiagonalBlockUnitLowerPos.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColumnGramDeterminantDiagonalBlockUnitLowerPos.lean#L29-L32

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

theorem GlobalTheory.IntBall.ColGramPos.lowerTri_det_one {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hu : ∀ i j, i < j → T i j = 0) (hd : ∀ i, T i i = 1) : T.det = 1 := by sorry
