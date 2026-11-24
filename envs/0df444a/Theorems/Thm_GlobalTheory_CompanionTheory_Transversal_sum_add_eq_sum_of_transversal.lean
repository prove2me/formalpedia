-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Transversal_sum_add_eq_sum_of_transversal
-- name    : GlobalTheory.CompanionTheory.Transversal.sum_add_eq_sum_of_transversal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:16:26.259023+00:00
-- url     : https://prove2.me/theorems/d85e32b1-fb34-4f86-80ec-ab919240b976
-- title:
--   Transversal: sum add eq sum of transversal
-- statement:
--   The Transversal construction uses the sum add eq sum of transversal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetSumTranslateInvariant.lean#L7-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetSumTranslateInvariant.lean#L7-L34

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetSumTranslateInvariant
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

theorem GlobalTheory.CompanionTheory.Transversal.sum_add_eq_sum_of_transversal : ∀ {X : Type} [AddCommGroup X] {M : Type} [AddCommMonoid M] {A H : AddSubgroup X}, H ≤ A → ∀ {T : Finset X}, (∀ t ∈ T, t ∈ A) → (∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) → ∀ (F : X → M), (∀ a, ∀ h ∈ H, F (a + h) = F a) → ∀ {a : X}, a ∈ A → ∑ t ∈ T, F (t + a) = ∑ t ∈ T, F t := by sorry
