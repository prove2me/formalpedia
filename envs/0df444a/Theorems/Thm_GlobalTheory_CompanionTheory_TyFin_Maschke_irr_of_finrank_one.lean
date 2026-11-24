-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_irr_of_finrank_one
-- name    : GlobalTheory.CompanionTheory.TyFin.Maschke.irr_of_finrank_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:18:38.925896+00:00
-- url     : https://prove2.me/theorems/d6a31a6f-2086-448b-b519-c3706431951e
-- title:
--   Maschke: irr of finrank one
-- statement:
--   The Maschke construction uses the irr of finrank one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MaschkeProperties.lean#L136-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MaschkeProperties.lean#L136-L181

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
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.TyFin.Maschke.irr_of_finrank_one [FiniteDimensional ℂ V] (ρ : Representation ℂ Γ V)
    (h : Module.finrank ℂ (Intw ρ ρ) = 1) : IsIrr ρ := by sorry
