-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_intw_eq_invariants
-- name    : GlobalTheory.CompanionTheory.TyFin.intw_eq_invariants
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:19:40.364897+00:00
-- url     : https://prove2.me/theorems/771be157-0dd8-40e1-b9b5-7bcf2f0032d1
-- title:
--   Ty Fin: intw eq invariants
-- statement:
--   The Ty Fin construction uses the intw eq invariants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntertwinerInnerProduct.lean#L9-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntertwinerInnerProduct.lean#L9-L25

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntertwinerInnerProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin

theorem GlobalTheory.CompanionTheory.TyFin.intw_eq_invariants {Γ : Type} [Group Γ] {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W) :
    Intw ρ σ = Representation.invariants (Representation.linHom ρ σ) := by sorry
