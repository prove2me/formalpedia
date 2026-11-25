-- Prove2me | Theorems.Thm_GlobalTheory_block_is_the_run
-- name    : GlobalTheory.block_is_the_run
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:53:02.653069+00:00
-- url     : https://prove2.me/theorems/1c94f82f-37ef-56e5-bb63-c058ba4d2363
-- title:
--   Global Theory: block is the run
-- statement:
--   The Global Theory construction uses the block is the run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BlockIsTheRun.lean#L5-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BlockIsTheRun.lean#L5-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BlockIsTheRun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.block_is_the_run : ∀ (n p t : ℕ) (a : ℕ → ℤ) (c : ℤ), (∀ i j, i ≤ j → j < n → a j ≤ a i) →
    p + t ≤ n → p < t → n - (p + t) < t → (∀ j, p ≤ j → j < p + t → a j = a p) →
    (1 ≤ p → a p < a (p - 1)) → (p + t < n → a (p + t) < a p) →
    (∀ i < t, ∃ j < n, a j - j = c - i) → c = a p - p := by sorry
