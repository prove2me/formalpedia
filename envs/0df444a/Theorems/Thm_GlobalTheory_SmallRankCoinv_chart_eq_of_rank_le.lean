-- Prove2me | Theorems.Thm_GlobalTheory_SmallRankCoinv_chart_eq_of_rank_le
-- name    : GlobalTheory.SmallRankCoinv.chart_eq_of_rank_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:47:40.144054+00:00
-- url     : https://prove2.me/theorems/bf850ed5-8761-44a0-b632-85b4cf2accac
-- title:
--   Small Rank Coinv: chart eq of rank le
-- statement:
--   The Small Rank Coinv construction uses the chart eq of rank le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsFullRankSubMem.lean#L82-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsFullRankSubMem.lean#L82-L188

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShearGLTransposeMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankChartStackDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankChartBoundedCoefficients
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankChartShearInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNonzeroMinorOfRank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatPartitionOfUnity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatReindexRows
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsFullRankSubMem
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
open GlobalTheory GlobalTheory.SmallRankCoinv
open GlobalTheory.SplitFlip GlobalTheory.LocMod.Inhab ValuativeRel GlobalTheory.RankChart GlobalTheory.RankStrata

theorem GlobalTheory.SmallRankCoinv.chart_eq_of_rank_le : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D] [Nonempty T] (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ‖(ν ϖ : ℂ)‖ = 1 → 2 * Fintype.card R < Fintype.card D → ∀ (τ : R → D), ∀ f ∈ SB (Matrix (R ⊕ T) D k), (∀ Y : Matrix (R ⊕ T) D k, f Y ≠ 0 → (Y.submatrix Sum.inl τ).det ≠ 0) → ∃ Φ ∈ GlobalTheory.RankStrata.Nsp k (R ⊕ T) D ν, ∀ Y : Matrix (R ⊕ T) D k, Y.rank ≤ Fintype.card R → Φ Y = f Y := by sorry
