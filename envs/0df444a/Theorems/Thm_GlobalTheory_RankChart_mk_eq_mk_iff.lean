-- Prove2me | Theorems.Thm_GlobalTheory_RankChart_mk_eq_mk_iff
-- name    : GlobalTheory.RankChart.mk_eq_mk_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:14:05.061673+00:00
-- url     : https://prove2.me/theorems/d125b406-2971-42ac-8508-98d2391227c7
-- title:
--   Rank Chart: mk eq mk iff
-- statement:
--   The Rank Chart construction uses the mk eq mk iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ShearGLTransposeMul.lean#L99-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ShearGLTransposeMul.lean#L99-L102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShearGLTransposeMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Matrix
noncomputable section
open GlobalTheory GlobalTheory.RankChart
open GlobalTheory.SplitFlip GlobalTheory.LocMod.Inhab ValuativeRel

theorem GlobalTheory.RankChart.mk_eq_mk_iff {G : Type} [AddCommGroup G] (H L : AddSubgroup G) (x y : H) :
    (QuotientAddGroup.mk x : H ⧸ L.addSubgroupOf H) = QuotientAddGroup.mk y ↔ (x : G) - y ∈ L := by sorry
