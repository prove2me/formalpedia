-- Prove2me | Theorems.Thm_GlobalTheory_KSp_finite_det_line_zero
-- name    : GlobalTheory.KSp.finite_det_line_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:47:05.020751+00:00
-- url     : https://prove2.me/theorems/97800248-a05b-4e77-8fca-2e8f841973c4
-- title:
--   KSp: finite det line zero
-- statement:
--   The KSp construction uses the finite det line zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsTranslateInCell.lean#L13-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsTranslateInCell.lean#L13-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InCellIffDetNeZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianSplitUnitaryLowerBlockInvertibleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsTranslateInCell
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory GlobalTheory.KSp

theorem GlobalTheory.KSp.finite_det_line_zero {F E : Type} [Field F] [Field E] [Algebra F E] {ν : Type} [Fintype ν] [DecidableEq ν]
    (A B : Matrix ν ν E) (r₀ : F) (h : (A + algebraMap F E r₀ • B).det ≠ 0) :
    {r : F | (A + algebraMap F E r • B).det = 0}.Finite := by sorry
