-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PatGrp_exists_nat_wh
-- name    : GlobalTheory.CompanionTheory.PatGrp.exists_nat_wh
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:54:11.168458+00:00
-- url     : https://prove2.me/theorems/3637bb28-3f7f-4786-a2f9-b9b4212fbdc9
-- title:
--   Pat Grp: exists nat wh
-- statement:
--   The Pat Grp construction uses the exists nat wh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PatternGroupStatement.lean#L254-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PatternGroupStatement.lean#L254-L275

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

theorem GlobalTheory.CompanionTheory.PatGrp.exists_nat_wh (h : IsPat Φ) {E : ι → ι → K} (hE : IsPatChar Φ E) (ψ₀ : AddChar K ℂ)
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (GL ι K) V) : ∃ m : ℕ, wh Φ E ψ₀ ρ.character = m := by sorry
