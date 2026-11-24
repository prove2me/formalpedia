-- Prove2me | Theorems.Thm_GlobalTheory_RankChart_sum_ite_out
-- name    : GlobalTheory.RankChart.sum_ite_out
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:07.912581+00:00
-- url     : https://prove2.me/theorems/dfd64ad7-d396-43d5-bc1b-4396319b064b
-- title:
--   Rank Chart: sum ite out
-- statement:
--   The Rank Chart construction uses the sum ite out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ShearGLTransposeMul.lean#L131-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ShearGLTransposeMul.lean#L131-L151

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
open Classical

theorem GlobalTheory.RankChart.sum_ite_out {G : Type} [AddCommGroup G] (H H' : AddSubgroup G) [Fintype (H' ⧸ H.addSubgroupOf H')]
    (hHH' : H ≤ H') (c : ℂ) (x : G) :
    ∑ q : H' ⧸ H.addSubgroupOf H', (if x + ((q.out : H') : G) ∈ H then c else 0) = if x ∈ H' then c else 0 := by sorry
