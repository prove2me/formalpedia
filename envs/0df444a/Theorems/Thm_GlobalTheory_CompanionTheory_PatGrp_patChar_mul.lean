-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PatGrp_patChar_mul
-- name    : GlobalTheory.CompanionTheory.PatGrp.patChar_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:55.371775+00:00
-- url     : https://prove2.me/theorems/bff59133-3f11-4160-a512-3ba9b877fdc6
-- title:
--   Pat Grp: pat Char mul
-- statement:
--   The Pat Grp construction uses the pat Char mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PatternGroupStatement.lean#L197-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PatternGroupStatement.lean#L197-L218

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

theorem GlobalTheory.CompanionTheory.PatGrp.patChar_mul (h : IsPat Φ) {E : ι → ι → K} (hE : IsPatChar Φ E) (ψ₀ : AddChar K ℂ)
    {u v : GL ι K} (hu : u ∈ patSet K Φ) (hv : v ∈ patSet K Φ) :
    patChar E ψ₀ (u * v) = patChar E ψ₀ u * patChar E ψ₀ v := by sorry
