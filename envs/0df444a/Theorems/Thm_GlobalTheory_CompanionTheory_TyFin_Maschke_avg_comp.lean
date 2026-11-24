-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_avg_comp
-- name    : GlobalTheory.CompanionTheory.TyFin.Maschke.avg_comp
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:19:44.554263+00:00
-- url     : https://prove2.me/theorems/22d9f837-1fcb-4f2a-95c2-8415fe2598b9
-- title:
--   Maschke: avg comp
-- statement:
--   The Maschke construction uses the avg comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MaschkeProperties.lean#L71-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MaschkeProperties.lean#L71-L78

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

theorem GlobalTheory.CompanionTheory.TyFin.Maschke.avg_comp {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} (τ : Representation ℂ Γ U)
    {φ : V →ₗ[ℂ] W} (hφ : φ ∈ Intw ρ σ) (f : W →ₗ[ℂ] U) :
    avg σ τ f ∘ₗ φ = avg ρ τ (f ∘ₗ φ) := by sorry
