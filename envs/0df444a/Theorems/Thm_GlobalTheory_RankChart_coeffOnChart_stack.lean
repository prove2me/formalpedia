-- Prove2me | Theorems.Thm_GlobalTheory_RankChart_coeffOnChart_stack
-- name    : GlobalTheory.RankChart.coeffOnChart_stack
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:39:35.836715+00:00
-- url     : https://prove2.me/theorems/3c1cb914-00ea-43a9-bac6-2b92829bbf2e
-- title:
--   Rank Chart: coeff On Chart stack
-- statement:
--   The Rank Chart construction uses the coeff On Chart stack property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankChartBoundedCoefficients.lean#L19-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankChartBoundedCoefficients.lean#L19-L28

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

theorem GlobalTheory.RankChart.coeffOnChart_stack {k : Type} [Field k] {R T D : Type} [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T]
    [Fintype D] [DecidableEq D] (τ : R → D)
    (Y₁ : Matrix R D k) (C : Matrix T R k) (h : (Y₁.submatrix id τ).det ≠ 0) :
    coeffOnChart τ (stack Y₁ C) = C := by sorry
