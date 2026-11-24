-- Prove2me | Theorems.Thm_GlobalTheory_RankStrata_exists_fullRank_sub_mem_span
-- name    : GlobalTheory.RankStrata.exists_fullRank_sub_mem_span
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:19:48.786799+00:00
-- url     : https://prove2.me/theorems/7f1ebe79-f9ef-4026-b8ea-98487a04fd41
-- title:
--   Rank Strata: exists full Rank sub mem span
-- statement:
--   The Rank Strata construction uses the exists full Rank sub mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatFullRankModuloTranslates.lean#L15-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatFullRankModuloTranslates.lean#L15-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNonzeroMinorOfRankStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatPartitionOfUnityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatReindexRowsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatMinorSupportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatFullRankModuloTranslates
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
open GlobalTheory GlobalTheory.RankStrata

theorem GlobalTheory.RankStrata.exists_fullRank_sub_mem_span : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν ϖ : ℂ)) ^ m ≠ (r : ℂ)) →
    ∀ Ψ ∈ SB (Matrix (Fin n) (Fin d) k), ∃ Ψ₀ ∈ SB (Matrix (Fin n) (Fin d) k), (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≠ n → Ψ₀ Y = 0) ∧
      Ψ - Ψ₀ ∈ Submodule.span ℂ {Z | ∃ g : GL (Fin n) k, ∃ Ψ' ∈ SB (Matrix (Fin n) (Fin d) k), Z = GlobalTheory.SplitFlip.omB ν ν g 1 Ψ' - Ψ'} := by sorry
