-- Prove2me | Theorems.Thm_GlobalTheory_T_qExpansionCoeffsInSubring_ring_closed
-- name    : GlobalTheory.T.qExpansionCoeffsInSubring_ring_closed
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:55:24.096798+00:00
-- url     : https://prove2.me/theorems/61575a46-5cac-4dce-904b-c32c479f4938
-- title:
--   T: q Expansion Coeffs In Subring ring closed
-- statement:
--   The T construction uses the q Expansion Coeffs In Subring ring closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QExpansionCoeffsInSubringRingClosedStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QExpansionCoeffsInSubringRingClosedStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QExpansionCoeffsInSubringRingClosed
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QExpansionCoeffsInSubringRingClosedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.qExpansionCoeffsInSubring_ring_closed : ∀ (R : Subring ℂ) (N : ℕ), 0 < N → (∀ c ∈ R, QAll (· ∈ R) N fun _ => c) ∧ (∀ f g, QAll (· ∈ R) N f → QAll (· ∈ R) N g → QAll (· ∈ R) N fun τ => f τ + g τ) ∧ (∀ f g, QAll (· ∈ R) N f → QAll (· ∈ R) N g → QAll (· ∈ R) N fun τ => f τ - g τ) ∧ (∀ f g, QAll (· ∈ R) N f → QAll (· ∈ R) N g → QAll (· ∈ R) N fun τ => f τ * g τ) ∧ (∀ f (k : ℕ), QAll (· ∈ R) N f → QAll (· ∈ R) N fun τ => f τ ^ k) ∧ (∀ (κ : Type) (s : Finset κ) (f : κ → ℍ → ℂ), (∀ k ∈ s, QAll (· ∈ R) N (f k)) → (QAll (· ∈ R) N fun τ => ∑ k ∈ s, f k τ) ∧ QAll (· ∈ R) N fun τ => ∏ k ∈ s, f k τ) := by sorry
