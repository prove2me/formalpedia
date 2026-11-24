-- Prove2me | Theorems.Thm_GlobalTheory_KSp_transvRankOne_adm
-- name    : GlobalTheory.KSp.transvRankOne_adm
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:22:24.492022+00:00
-- url     : https://prove2.me/theorems/bd269178-e648-4205-8905-33cd61195582
-- title:
--   KSp: transv Rank One adm
-- statement:
--   The KSp construction uses the transv Rank One adm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHermitianSplitUnitaryLowerBlockInvertible.lean#L32-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHermitianSplitUnitaryLowerBlockInvertible.lean#L32-L41

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianSplitUnitaryLowerBlockInvertible
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
variable {k : Type} [Field k] {ν : Type} [Fintype ν] [DecidableEq ν]

theorem GlobalTheory.KSp.transvRankOne_adm (c : k →+* k) (S : Matrix ν ν k) (hS : Sᵀ = -S.map c) (j : ν) :
    (transvRankOne S j)ᵀ * S + S * (transvRankOne S j).map c = 0 := by sorry
