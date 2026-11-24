-- Prove2me | Theorems.Thm_GlobalTheory_Published_linnik_iff_exists_prime
-- name    : GlobalTheory.Published.linnik_iff_exists_prime
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:58:39.514573+00:00
-- url     : https://prove2.me/theorems/92ed586d-3690-4f42-91c0-e90fb18e0437
-- title:
--   Published: linnik iff exists prime
-- statement:
--   The Published construction uses the linnik iff exists prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/PrimesInProgressionNonempty.lean#L20-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/PrimesInProgressionNonempty.lean#L20-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_PrimesInProgressionNonempty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Published

theorem GlobalTheory.Published.linnik_iff_exists_prime : _root_.GlobalTheory.Published.Linnik ↔
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧ ∀ a q : ℕ, 1 ≤ a → 1 ≤ q → a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ C * (q : ℝ) ^ L := by sorry
