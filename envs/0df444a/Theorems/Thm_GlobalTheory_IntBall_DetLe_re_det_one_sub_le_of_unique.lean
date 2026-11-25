-- Prove2me | Theorems.Thm_GlobalTheory_IntBall_DetLe_re_det_one_sub_le_of_unique
-- name    : GlobalTheory.IntBall.DetLe.re_det_one_sub_le_of_unique
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:45:55.021357+00:00
-- url     : https://prove2.me/theorems/4b8075f1-d212-4c55-a51f-32b6f50aa341
-- title:
--   Det Le: re det one sub le of unique
-- statement:
--   The Det Le construction uses the re det one sub le of unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DetOneSubOffDiagonalBlockGramLeOneBall.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DetOneSubOffDiagonalBlockGramLeOneBall.lean#L10-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetOneSubOffDiagonalBlockGramLeOneBall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
open GlobalTheory GlobalTheory.IntBall GlobalTheory.IntBall.DetLe

theorem GlobalTheory.IntBall.DetLe.re_det_one_sub_le_of_unique {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι] [Unique ι]
    (Z : Matrix κ ι ℂ) : ((1 - Zᴴ * Z).det).re ≤ 1 := by sorry
