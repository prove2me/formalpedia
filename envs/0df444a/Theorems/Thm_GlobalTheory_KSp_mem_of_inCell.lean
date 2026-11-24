-- Prove2me | Theorems.Thm_GlobalTheory_KSp_mem_of_inCell
-- name    : GlobalTheory.KSp.mem_of_inCell
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:08:45.976743+00:00
-- url     : https://prove2.me/theorems/96f9536b-1744-4d2f-ab7f-7478b889eb99
-- title:
--   KSp: mem of in Cell
-- statement:
--   The KSp construction uses the mem of in Cell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SiegelParabolicWeylElementGenerateUnitary.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SiegelParabolicWeylElementGenerateUnitary.lean#L11-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsTranslateInCellStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SiegelParabolicWeylElementGenerateUnitary
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

theorem GlobalTheory.KSp.mem_of_inCell {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
    {ν : Type} [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E)))
    (hP : sieg c ν ≤ U) (hw : weyl c ν ∈ U) {g : UG c (stdJ ν E)} (hg : InCell c g) : g ∈ U := by sorry
