-- Prove2me | Theorems.Thm_GlobalTheory_RankChart_coeffOnChart_continuousOn
-- name    : GlobalTheory.RankChart.coeffOnChart_continuousOn
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:41:19.790299+00:00
-- url     : https://prove2.me/theorems/16cdeb2c-0209-4189-bd3f-db12268dbdf0
-- title:
--   Rank Chart: coeff On Chart continuous On
-- statement:
--   The Rank Chart construction uses the coeff On Chart continuous On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankChartBoundedCoefficients.lean#L30-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankChartBoundedCoefficients.lean#L30-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShearGLTransposeMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IndicatorBoxEqCharSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankChartBoundedCoefficients
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
open ValuativeRel

theorem GlobalTheory.RankChart.coeffOnChart_continuousOn {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    [ContinuousInv₀ k] {R T D : Type} [Fintype R] [DecidableEq R] (τ : R → D) :
    ContinuousOn (coeffOnChart (T := T) (k := k) τ) {Y | (Y.submatrix Sum.inl τ).det ≠ 0} := by sorry
