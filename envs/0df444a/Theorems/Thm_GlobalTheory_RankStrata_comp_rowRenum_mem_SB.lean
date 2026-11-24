-- Prove2me | Theorems.Thm_GlobalTheory_RankStrata_comp_rowRenum_mem_SB
-- name    : GlobalTheory.RankStrata.comp_rowRenum_mem_SB
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:14:40.759339+00:00
-- url     : https://prove2.me/theorems/79609ef1-a2bb-4ecd-9f9e-5e7c498a5ffa
-- title:
--   Rank Strata: comp row Renum mem SB
-- statement:
--   The Rank Strata construction uses the comp row Renum mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatReindexRows.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatReindexRows.lean#L21-L24

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

theorem GlobalTheory.RankStrata.comp_rowRenum_mem_SB (e : A ≃ A') {f : Matrix A' D k → ℂ} (hf : f ∈ SB (Matrix A' D k)) :
    (fun Y : Matrix A D k => f (Y.submatrix e.symm id)) ∈ SB (Matrix A D k) := by sorry
