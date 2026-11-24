-- Prove2me | Theorems.Thm_GlobalTheory_RankChart_sum_shift_out
-- name    : GlobalTheory.RankChart.sum_shift_out
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:04.200284+00:00
-- url     : https://prove2.me/theorems/ae22e9fa-d12d-43e8-841b-06b262f32c63
-- title:
--   Rank Chart: sum shift out
-- statement:
--   The Rank Chart construction uses the sum shift out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ShearGLTransposeMul.lean#L106-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ShearGLTransposeMul.lean#L106-L127

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

theorem GlobalTheory.RankChart.sum_shift_out {G : Type} [AddCommGroup G] (F : G → ℂ) (H L : AddSubgroup G)
    [Fintype (H ⧸ L.addSubgroupOf H)] (hL : ∀ x y, y - x ∈ L → F y = F x) (hH : ∀ x, F x ≠ 0 → x ∈ H) (x : G) :
    ∑ q : H ⧸ L.addSubgroupOf H, F (x + ((q.out : H) : G)) =
      if x ∈ H then ∑ q : H ⧸ L.addSubgroupOf H, F ((q.out : H) : G) else 0 := by sorry
