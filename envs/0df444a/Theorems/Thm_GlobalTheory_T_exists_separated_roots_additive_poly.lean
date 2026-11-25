-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_separated_roots_additive_poly
-- name    : GlobalTheory.T.exists_separated_roots_additive_poly
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:39:15.506213+00:00
-- url     : https://prove2.me/theorems/f3bcb336-f078-4388-9750-6d04861432c8
-- title:
--   T: exists separated roots additive poly
-- statement:
--   The T construction uses the exists separated roots additive poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SeparatedRootsAdditivePolyStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SeparatedRootsAdditivePolyStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SeparatedRootsAdditivePoly
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SeparatedRootsAdditivePolyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_separated_roots_additive_poly : ∀ (l : ℕ) [Fact l.Prime] (E M h : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ), M + h ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖a (M + h)‖ = 1 → 0 < ρ → ρ < 1 → ‖a M‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ → (∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) → ∃ Z : Finset ℂ_[l], l ^ h ≤ Z.card ∧ (∀ W ∈ Z, ‖W‖ ≤ 1 ∧ ∑ k ∈ Finset.range (E + 1), a k * W ^ l ^ k = 0) ∧ ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖ := by sorry
