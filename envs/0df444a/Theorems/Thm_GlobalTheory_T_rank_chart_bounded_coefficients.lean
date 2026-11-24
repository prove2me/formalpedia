-- Prove2me | Theorems.Thm_GlobalTheory_T_rank_chart_bounded_coefficients
-- name    : GlobalTheory.T.rank_chart_bounded_coefficients
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:48:02.509868+00:00
-- url     : https://prove2.me/theorems/dbc7c4f4-1b91-4233-a965-ef35a027c63a
-- title:
--   T: rank chart bounded coefficients
-- statement:
--   The T construction uses the rank chart bounded coefficients property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankChartBoundedCoefficientsStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankChartBoundedCoefficientsStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankChartBoundedCoefficients
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShearGLTransposeMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankChartBoundedCoefficientsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.rank_chart_bounded_coefficients : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D] (τ : R → D), ∀ f ∈ SB (Matrix (R ⊕ T) D k), (∀ Y : Matrix (R ⊕ T) D k, f Y ≠ 0 → (Y.submatrix Sum.inl τ).det ≠ 0) → ∃ a : kˣ, ∀ (Y₁ : Matrix R D k) (C : Matrix T R k), f (GlobalTheory.RankChart.stack Y₁ C) ≠ 0 → C ∈ GlobalTheory.LocMod.Inhab.box T R a := by sorry
