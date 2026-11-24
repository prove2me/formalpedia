-- Prove2me | Theorems.Thm_GlobalTheory_KSp_transvRankOne_mulVec
-- name    : GlobalTheory.KSp.transvRankOne_mulVec
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:23:55.624374+00:00
-- url     : https://prove2.me/theorems/7949d534-1367-4e68-b261-7d01143a96e8
-- title:
--   KSp: transv Rank One mul Vec
-- statement:
--   The KSp construction uses the transv Rank One mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHermitianSplitUnitaryLowerBlockInvertible.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHermitianSplitUnitaryLowerBlockInvertible.lean#L43-L48

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

theorem GlobalTheory.KSp.transvRankOne_mulVec (S : Matrix ν ν k) (j : ν) (v : ν → k) :
    transvRankOne S j *ᵥ v = Pi.single j ((v ᵥ* S) j) := by sorry
