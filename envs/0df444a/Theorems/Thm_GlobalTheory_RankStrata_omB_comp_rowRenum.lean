-- Prove2me | Theorems.Thm_GlobalTheory_RankStrata_omB_comp_rowRenum
-- name    : GlobalTheory.RankStrata.omB_comp_rowRenum
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:14:42.756841+00:00
-- url     : https://prove2.me/theorems/41f8a6c2-514a-4f89-882b-e50f7454bcf5
-- title:
--   Rank Strata: om B comp row Renum
-- statement:
--   The Rank Strata construction uses the om B comp row Renum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatReindexRows.lean#L36-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatReindexRows.lean#L36-L48

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

theorem GlobalTheory.RankStrata.omB_comp_rowRenum (ν : kˣ →* ℂˣ) (e : A ≃ A') (g : GL A' k) (Ψ : Matrix A' D k → ℂ) :
    (fun Y : Matrix A D k => GlobalTheory.SplitFlip.omB ν ν g 1 Ψ (Y.submatrix e.symm id)) =
      GlobalTheory.SplitFlip.omB ν ν (glRenum e g) 1 (fun Y : Matrix A D k => Ψ (Y.submatrix e.symm id)) := by sorry
