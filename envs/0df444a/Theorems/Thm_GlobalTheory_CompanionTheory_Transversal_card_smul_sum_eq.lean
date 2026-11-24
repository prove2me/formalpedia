-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Transversal_card_smul_sum_eq
-- name    : GlobalTheory.CompanionTheory.Transversal.card_smul_sum_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:51.402402+00:00
-- url     : https://prove2.me/theorems/d143ddfd-be1e-4932-aa98-59c8ef424824
-- title:
--   Transversal: card smul sum eq
-- statement:
--   The Transversal construction uses the card smul sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetSumsProportionalCard.lean#L40-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetSumsProportionalCard.lean#L40-L54

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetSumsProportionalCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Transversal

theorem GlobalTheory.CompanionTheory.Transversal.card_smul_sum_eq {X : Type} [AddCommGroup X] {M : Type} [AddCommGroup M] [Module ℂ M]
    {A H H' : AddSubgroup X} (hH : H ≤ A) (hH' : H' ≤ A) {T T' : Finset X}
    (hTA : ∀ t ∈ T, t ∈ A) (hT : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H)
    (hTA' : ∀ t ∈ T', t ∈ A) (hT' : ∀ a ∈ A, ∃! t, t ∈ T' ∧ a - t ∈ H')
    (F : X → M) (hF : ∀ a, ∀ h ∈ H, F (a + h) = F a) (hF' : ∀ a, ∀ h ∈ H', F (a + h) = F a) :
    (T'.card : ℂ) • ∑ t ∈ T, F t = (T.card : ℂ) • ∑ t ∈ T', F t := by sorry
