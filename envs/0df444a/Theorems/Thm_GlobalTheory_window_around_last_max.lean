-- Prove2me | Theorems.Thm_GlobalTheory_window_around_last_max
-- name    : GlobalTheory.window_around_last_max
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:24:34.918163+00:00
-- url     : https://prove2.me/theorems/9e88caf7-683c-4844-b809-8dc9a085c536
-- title:
--   Global Theory: window around last max
-- statement:
--   The Global Theory construction uses the window around last max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WindowAroundLastMaxNullSequence.lean#L6-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WindowAroundLastMaxNullSequence.lean#L6-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WindowAroundLastMaxNullSequence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.window_around_last_max : ∀ (β : ℤ → ℝ) (c : ℝ) (h : ℕ), 0 < c → (∀ k, 0 ≤ β k) → (∃ k, β k ≠ 0) → Filter.Tendsto β Filter.cofinite (nhds 0) → ∃ (D E M : ℕ), h ≤ D ∧ M + h ≤ E ∧ 0 < β ((M + h : ℕ) - D) ∧ (∀ k, β k ≤ β ((M + h : ℕ) - D)) ∧ (∀ k, ((M + h : ℕ) : ℤ) - D < k → β k < β ((M + h : ℕ) - D)) ∧ ∀ k : ℤ, (k < -(D : ℤ) ∨ (E : ℤ) - D < k) → β k ≤ c * β ((M + h : ℕ) - D) := by sorry
