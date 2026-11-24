-- Prove2me | Theorems.Thm_GlobalTheory_multiset_many_separated_points
-- name    : GlobalTheory.multiset_many_separated_points
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:12:02.153351+00:00
-- url     : https://prove2.me/theorems/a0fca79e-2e77-4d61-aa12-861e2331644b
-- title:
--   Global Theory: multiset many separated points
-- statement:
--   The Global Theory construction uses the multiset many separated points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MultisetManySeparatedPoints.lean#L7-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MultisetManySeparatedPoints.lean#L7-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MultisetManySeparatedPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Classical
open GlobalTheory

theorem GlobalTheory.multiset_many_separated_points : ∀ (K : Type) [NormedAddCommGroup K] (s : Multiset K) (ρ : ℝ) (A B : ℕ), 0 ≤ ρ → 0 < B → A * B ≤ Multiset.card s → (∀ W ∈ s, Multiset.card (s.filter fun z => ‖z - W‖ ≤ ρ) ≤ B) → ∃ Z : Finset K, A ≤ Z.card ∧ (∀ W ∈ Z, W ∈ s) ∧ ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖ := by sorry
