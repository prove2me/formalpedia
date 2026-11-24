-- Prove2me | Theorems.Thm_GlobalTheory_RankChart_exists_eq_stack
-- name    : GlobalTheory.RankChart.exists_eq_stack
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:16.08578+00:00
-- url     : https://prove2.me/theorems/75837587-8cce-4fb3-88d1-21ff01e3603a
-- title:
--   Rank Chart: exists eq stack
-- statement:
--   The Rank Chart construction uses the exists eq stack property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankChartStackDecomposition.lean#L11-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankChartStackDecomposition.lean#L11-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShearGLTransposeMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankChartStackDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Matrix
open GlobalTheory GlobalTheory.RankChart

theorem GlobalTheory.RankChart.exists_eq_stack (k : Type) [Field k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T]
    [DecidableEq T] [Fintype D] [DecidableEq D] (τ : R → D) (Y : Matrix (R ⊕ T) D k)
    (hrank : Y.rank ≤ Fintype.card R) (hdet : (Y.submatrix Sum.inl τ).det ≠ 0) :
    ∃ C : Matrix T R k, Y = GlobalTheory.RankChart.stack Y.toRows₁ C := by sorry
