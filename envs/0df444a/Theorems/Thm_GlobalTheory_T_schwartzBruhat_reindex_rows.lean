-- Prove2me | Theorems.Thm_GlobalTheory_T_schwartzBruhat_reindex_rows
-- name    : GlobalTheory.T.schwartzBruhat_reindex_rows
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:57:31.64346+00:00
-- url     : https://prove2.me/theorems/a1af9178-f64f-4c31-a878-fbc34f234108
-- title:
--   T: schwartz Bruhat reindex rows
-- statement:
--   The T construction uses the schwartz Bruhat reindex rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatReindexRowsStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatReindexRowsStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatReindexRows
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatReindexRowsStatement
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

theorem GlobalTheory.T.schwartzBruhat_reindex_rows : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A A' D : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (ν : kˣ →* ℂˣ) (e : A ≃ A'), (∀ f ∈ SB (Matrix A' D k), (fun Y : Matrix A D k => f (Y.submatrix e.symm id)) ∈ SB (Matrix A D k)) ∧ (∀ f ∈ GlobalTheory.RankStrata.Nsp k A' D ν, (fun Y : Matrix A D k => f (Y.submatrix e.symm id)) ∈ GlobalTheory.RankStrata.Nsp k A D ν) := by sorry
