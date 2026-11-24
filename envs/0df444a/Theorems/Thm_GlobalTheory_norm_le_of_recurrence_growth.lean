-- Prove2me | Theorems.Thm_GlobalTheory_norm_le_of_recurrence_growth
-- name    : GlobalTheory.norm_le_of_recurrence_growth
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:12:57.839196+00:00
-- url     : https://prove2.me/theorems/4e637f77-f648-4c15-9fea-72c770d47cb1
-- title:
--   Global Theory: norm le of recurrence growth
-- statement:
--   The Global Theory construction uses the norm le of recurrence growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/NormLeOfRecurrenceGrowth.lean#L7-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/NormLeOfRecurrenceGrowth.lean#L7-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_NormLeOfRecurrenceGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory

theorem GlobalTheory.norm_le_of_recurrence_growth : ∀ (β : Multiset ℂ) (a : ℕ → ℂ) (C B : ℝ) (m : ℕ), 0 < B → a 0 = 1 → (∀ n, 1 ≤ n → ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * β.esymm k * a (n - k) = 0) → (∀ n, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ m * B ^ n) → ∀ b ∈ β, ‖b‖ ≤ B := by sorry
