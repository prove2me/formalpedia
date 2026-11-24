-- Prove2me | Theorems.Thm_GlobalTheory_RankStrata_sub_mem_Nsp
-- name    : GlobalTheory.RankStrata.sub_mem_Nsp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:47.950747+00:00
-- url     : https://prove2.me/theorems/8afee2ce-1199-4a8f-9834-00ee94f9f942
-- title:
--   Rank Strata: sub mem Nsp
-- statement:
--   The Rank Strata construction uses the sub mem Nsp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubMemNsp.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubMemNsp.lean#L24-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
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
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}

theorem GlobalTheory.RankStrata.sub_mem_Nsp {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν : kˣ →* ℂˣ)
    (g : GL A k) {Ψ : Matrix A D k → ℂ} (hΨ : Ψ ∈ SB (Matrix A D k)) :
    GlobalTheory.SplitFlip.omB ν ν g 1 Ψ - Ψ ∈ Nsp k A D ν := by sorry
