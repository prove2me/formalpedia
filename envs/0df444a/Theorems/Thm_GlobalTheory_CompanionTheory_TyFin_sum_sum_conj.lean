-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_sum_sum_conj
-- name    : GlobalTheory.CompanionTheory.TyFin.sum_sum_conj
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:18:59.519528+00:00
-- url     : https://prove2.me/theorems/740fdc5b-e83d-4c6d-a98c-0a7849b8943f
-- title:
--   Ty Fin: sum sum conj
-- statement:
--   The Ty Fin construction uses the sum sum conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FrobeniusReciprocityInnerProduct.lean#L8-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FrobeniusReciprocityInnerProduct.lean#L8-L13

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FrobeniusReciprocityInnerProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin

theorem GlobalTheory.CompanionTheory.TyFin.sum_sum_conj {Γ : Type} [Group Γ] [Fintype Γ] (f : Γ → ℂ) :
    ∑ g, ∑ x, f (x * g * x⁻¹) = (Fintype.card Γ : ℂ) * ∑ h, f h := by sorry
