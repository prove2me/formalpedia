-- Prove2me | Theorems.Thm_GlobalTheory_first_term_le_of_logConcave_blocks
-- name    : GlobalTheory.first_term_le_of_logConcave_blocks
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:50:41.482848+00:00
-- url     : https://prove2.me/theorems/88f66aa2-cea4-487b-abf7-c8b8869d316c
-- title:
--   Global Theory: first term le of log Concave blocks
-- statement:
--   The Global Theory construction uses the first term le of log Concave blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LogConcaveMultiplicativeGrowthBound.lean#L22-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LogConcaveMultiplicativeGrowthBound.lean#L22-L91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogConcaveMultiplicativeGrowthBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory

theorem GlobalTheory.first_term_le_of_logConcave_blocks :
    ∀ (g : ℕ → ℕ) (e C B : ℕ), 1 ≤ e → g 0 = 1 → (∀ n, 0 < g n) →
    (∀ k, g (k + 2) * g k ≤ g (k + 1) ^ 2) → (∀ j, g (e * (j + 1)) = g (e * j) * g e) →
    (∀ n, g n ≤ C * B ^ n) → g 1 ≤ B := by sorry
