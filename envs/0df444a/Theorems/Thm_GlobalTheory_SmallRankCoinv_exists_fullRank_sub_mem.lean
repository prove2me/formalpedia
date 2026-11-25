-- Prove2me | Theorems.Thm_GlobalTheory_SmallRankCoinv_exists_fullRank_sub_mem
-- name    : GlobalTheory.SmallRankCoinv.exists_fullRank_sub_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:26:00.389516+00:00
-- url     : https://prove2.me/theorems/cf9e06ef-9f73-55a8-9ce3-925557ada035
-- title:
--   Small Rank Coinv: exists full Rank sub mem
-- statement:
--   The Small Rank Coinv construction uses the exists full Rank sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsFullRankSubMem.lean#L190-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsFullRankSubMem.lean#L190-L270

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

theorem GlobalTheory.SmallRankCoinv.exists_fullRank_sub_mem : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ‖(ν ϖ : ℂ)‖ = 1 → 2 * n ≤ d + 1 →
    ∀ Ψ ∈ SB (Matrix (Fin n) (Fin d) k), ∃ Ψ₀ ∈ SB (Matrix (Fin n) (Fin d) k), (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≠ n → Ψ₀ Y = 0) ∧
      Ψ - Ψ₀ ∈ Submodule.span ℂ {Z | ∃ g : GL (Fin n) k, ∃ Ψ' ∈ SB (Matrix (Fin n) (Fin d) k), Z = GlobalTheory.SplitFlip.omB ν ν g 1 Ψ' - Ψ'} := by sorry
