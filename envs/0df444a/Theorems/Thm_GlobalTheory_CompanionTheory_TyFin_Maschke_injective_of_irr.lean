-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_injective_of_irr
-- name    : GlobalTheory.CompanionTheory.TyFin.Maschke.injective_of_irr
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:18:47.535057+00:00
-- url     : https://prove2.me/theorems/100e6980-c370-43aa-80bf-fac08d61c444
-- title:
--   Maschke: injective of irr
-- statement:
--   The Maschke construction uses the injective of irr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MaschkeProperties.lean#L110-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MaschkeProperties.lean#L110-L118

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
variable {Γ : Type} [Group Γ]
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.CompanionTheory.TyFin.Maschke.injective_of_irr {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {φ : V →ₗ[ℂ] W}
    (hρ : IsIrr ρ) (hφ : φ ∈ Intw ρ σ) (h0 : φ ≠ 0) : Function.Injective φ := by sorry
