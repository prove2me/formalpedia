-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_exists_right_inverse
-- name    : GlobalTheory.CompanionTheory.TyFin.Maschke.exists_right_inverse
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:18:44.110805+00:00
-- url     : https://prove2.me/theorems/dcbdb8b0-df3d-4792-9959-a8309039629a
-- title:
--   Maschke: exists right inverse
-- statement:
--   The Maschke construction uses the exists right inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MaschkeProperties.lean#L96-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MaschkeProperties.lean#L96-L101

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

theorem GlobalTheory.CompanionTheory.TyFin.Maschke.exists_right_inverse {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {φ : V →ₗ[ℂ] W}
    (hφ : φ ∈ Intw ρ σ) (hsurj : Function.Surjective φ) :
    ∃ ψ ∈ Intw σ ρ, φ ∘ₗ ψ = LinearMap.id := by sorry
