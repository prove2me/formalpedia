-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PatGrp_patChar_one
-- name    : GlobalTheory.CompanionTheory.PatGrp.patChar_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:54:20.914845+00:00
-- url     : https://prove2.me/theorems/be8b9169-8a24-4555-88cc-a6c0ec0a25c1
-- title:
--   Pat Grp: pat Char one
-- statement:
--   The Pat Grp construction uses the pat Char one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PatternGroupStatement.lean#L220-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PatternGroupStatement.lean#L220-L223

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PatGrp
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Φ : ι → ι → Prop}

theorem GlobalTheory.CompanionTheory.PatGrp.patChar_one (h : IsPat Φ) {E : ι → ι → K} (hE : IsPatChar Φ E) (ψ₀ : AddChar K ℂ) :
    patChar E ψ₀ (1 : GL ι K) = 1 := by sorry
