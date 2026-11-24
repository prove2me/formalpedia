-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_comp_mem
-- name    : GlobalTheory.CompanionTheory.TyFin.Maschke.comp_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:18:37.994483+00:00
-- url     : https://prove2.me/theorems/45aa60c3-9888-4598-a201-d527d67f074e
-- title:
--   Maschke: comp mem
-- statement:
--   The Maschke construction uses the comp mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MaschkeProperties.lean#L63-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MaschkeProperties.lean#L63-L69

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.Maschke
variable {Γ : Type} [Group Γ] [Fintype Γ]
variable {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

theorem GlobalTheory.CompanionTheory.TyFin.Maschke.comp_mem {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {τ : Representation ℂ Γ U}
    {φ : V →ₗ[ℂ] W} {ψ : W →ₗ[ℂ] U} (hφ : φ ∈ Intw ρ σ) (hψ : ψ ∈ Intw σ τ) :
    ψ ∘ₗ φ ∈ Intw ρ τ := by sorry
