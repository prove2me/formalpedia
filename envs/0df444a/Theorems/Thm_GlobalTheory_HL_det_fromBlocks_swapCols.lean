-- Prove2me | Theorems.Thm_GlobalTheory_HL_det_fromBlocks_swapCols
-- name    : GlobalTheory.HL.det_fromBlocks_swapCols
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:15:41.030497+00:00
-- url     : https://prove2.me/theorems/9f5c3f23-fe45-46f0-b0a5-0b38a3dc81e8
-- title:
--   HL: det from Blocks swap Cols
-- statement:
--   The HL construction uses the det from Blocks swap Cols property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DetGramTwoFrames.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DetGramTwoFrames.lean#L9-L20

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetGramTwoFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL

theorem GlobalTheory.HL.det_fromBlocks_swapCols {R n : Type} [CommRing R] [Fintype n] [DecidableEq n]
    (A B C D : Matrix n n R) :
    (Matrix.fromBlocks A B C D).det = (-1) ^ Fintype.card n * (Matrix.fromBlocks B A D C).det := by sorry
