-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_nonempty_iso_iff_intertwiner
-- name    : GlobalTheory.CompanionTheory.TyFin.nonempty_iso_iff_intertwiner
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:18:52.69298+00:00
-- url     : https://prove2.me/theorems/5c5b2b5e-272f-43e2-9b9b-8bf3887a593f
-- title:
--   Ty Fin: nonempty iso iff intertwiner
-- statement:
--   The Ty Fin construction uses the nonempty iso iff intertwiner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SimpleIffIrreducible.lean#L11-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SimpleIffIrreducible.lean#L11-L33

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_Basics
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory ReciprocityTheory.Ty.Fin PI.GreenHCLabel
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin

theorem GlobalTheory.CompanionTheory.TyFin.nonempty_iso_iff_intertwiner {Γ : Type} [Group Γ] (τ σ : FDRep ℂ Γ) :
    Nonempty (τ ≅ σ) ↔ ∃ e : τ ≃ₗ[ℂ] σ, ∀ γ v, e (τ.ρ γ v) = σ.ρ γ (e v) := by sorry
