-- Prove2me | Theorems.Thm_GlobalTheory_RankStrata_rowRenum_SB_Nsp
-- name    : GlobalTheory.RankStrata.rowRenum_SB_Nsp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:47.423869+00:00
-- url     : https://prove2.me/theorems/714fd6d5-fc59-488c-9dc4-33eb992b4aea
-- title:
--   Rank Strata: row Renum SB Nsp
-- statement:
--   The Rank Strata construction uses the row Renum SB Nsp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatReindexRows.lean#L50-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatReindexRows.lean#L50-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatReindexRows
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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]

theorem GlobalTheory.RankStrata.rowRenum_SB_Nsp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A A' D : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (ν : kˣ →* ℂˣ) (e : A ≃ A'),
    (∀ f ∈ SB (Matrix A' D k), (fun Y : Matrix A D k => f (Y.submatrix e.symm id)) ∈ SB (Matrix A D k)) ∧
    (∀ f ∈ GlobalTheory.RankStrata.Nsp k A' D ν,
      (fun Y : Matrix A D k => f (Y.submatrix e.symm id)) ∈ GlobalTheory.RankStrata.Nsp k A D ν) := by sorry
