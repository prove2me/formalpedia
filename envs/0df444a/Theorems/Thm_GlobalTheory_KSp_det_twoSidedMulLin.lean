-- Prove2me | Theorems.Thm_GlobalTheory_KSp_det_twoSidedMulLin
-- name    : GlobalTheory.KSp.det_twoSidedMulLin
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:22:45.060886+00:00
-- url     : https://prove2.me/theorems/40b645b0-3393-4d48-8441-3960c69d79a9
-- title:
--   KSp: det two Sided Mul Lin
-- statement:
--   The KSp construction uses the det two Sided Mul Lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DetRestrictScalarsTwoSidedMatrixMul.lean#L18-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DetRestrictScalarsTwoSidedMatrixMul.lean#L18-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetRestrictScalarsTwoSidedMatrixMul
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
noncomputable section
open GlobalTheory GlobalTheory.KSp

theorem GlobalTheory.KSp.det_twoSidedMulLin {E : Type} [Field E] {α ν : Type} [Fintype α] [DecidableEq α]
    [Fintype ν] [DecidableEq ν] (u : Matrix α α E) (a : Matrix ν ν E) :
    LinearMap.det (twoSidedMulLin u a) = u.det ^ Fintype.card ν * a.det ^ Fintype.card α := by sorry
