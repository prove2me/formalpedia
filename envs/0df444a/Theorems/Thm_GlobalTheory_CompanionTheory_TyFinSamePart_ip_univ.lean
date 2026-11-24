-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFinSamePart_ip_univ
-- name    : GlobalTheory.CompanionTheory.TyFinSamePart.ip_univ
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:18:26.779725+00:00
-- url     : https://prove2.me/theorems/63d42767-e121-46cc-be98-8d6bb6e24593
-- title:
--   Ty Fin Same Part: ip univ
-- statement:
--   The Ty Fin Same Part construction uses the ip univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SamePartitionStatement.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SamePartitionStatement.lean#L44-L46

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SamePartitionStatement
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFinSamePart

theorem GlobalTheory.CompanionTheory.TyFinSamePart.ip_univ {Γ : Type} [Group Γ] [Fintype Γ] (a c : Γ → ℂ) :
    ip Set.univ a c = (Fintype.card Γ : ℂ)⁻¹ * ∑ g, a g⁻¹ * c g := by sorry
