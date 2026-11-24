-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFinSamePart_ip_coe
-- name    : GlobalTheory.CompanionTheory.TyFinSamePart.ip_coe
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:18:35.092855+00:00
-- url     : https://prove2.me/theorems/a2e6be96-4a4f-4425-97f8-74ecabb74461
-- title:
--   Ty Fin Same Part: ip coe
-- statement:
--   The Ty Fin Same Part construction uses the ip coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SamePartitionStatement.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SamePartitionStatement.lean#L33-L42

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

theorem GlobalTheory.CompanionTheory.TyFinSamePart.ip_coe {Γ : Type} [Group Γ] [Fintype Γ] (H : Subgroup Γ) [Fintype H] (a c : Γ → ℂ) :
    ip (H : Set Γ) a c = (Fintype.card H : ℂ)⁻¹ * ∑ h : H, a (h : Γ)⁻¹ * c h := by sorry
