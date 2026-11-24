-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_finset_separated_of_multiset_bounded_cluster
-- name    : GlobalTheory.T.exists_finset_separated_of_multiset_bounded_cluster
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:35:40.325129+00:00
-- url     : https://prove2.me/theorems/eed75590-c29a-4cdf-bbf8-70ed03e7ec8a
-- title:
--   T: exists finset separated of multiset bounded cluster
-- statement:
--   The T construction uses the exists finset separated of multiset bounded cluster property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MultisetManySeparatedPointsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MultisetManySeparatedPointsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MultisetManySeparatedPoints
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MultisetManySeparatedPointsStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_finset_separated_of_multiset_bounded_cluster : ∀ (K : Type) [NormedAddCommGroup K] (s : Multiset K) (ρ : ℝ) (A B : ℕ), 0 ≤ ρ → 0 < B → A * B ≤ Multiset.card s → (∀ W ∈ s, Multiset.card (s.filter fun z => ‖z - W‖ ≤ ρ) ≤ B) → ∃ Z : Finset K, A ≤ Z.card ∧ (∀ W ∈ Z, W ∈ s) ∧ ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖ := by sorry
