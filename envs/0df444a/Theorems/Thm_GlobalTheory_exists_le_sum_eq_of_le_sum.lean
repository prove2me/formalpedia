-- Prove2me | Theorems.Thm_GlobalTheory_exists_le_sum_eq_of_le_sum
-- name    : GlobalTheory.exists_le_sum_eq_of_le_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:26:36.040655+00:00
-- url     : https://prove2.me/theorems/57720f8e-c6ce-4074-9b62-5037f8641e8b
-- title:
--   Global Theory: exists le sum eq of le sum
-- statement:
--   The Global Theory construction uses the exists le sum eq of le sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsCutIntoBoundedGroupsFinset.lean#L5-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsCutIntoBoundedGroupsFinset.lean#L5-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCutIntoBoundedGroupsFinset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_le_sum_eq_of_le_sum (S : Finset ℕ) (e : ℕ → ℕ) :
    ∀ n, n ≤ ∑ k ∈ S, e k →
      ∃ f : ℕ → ℕ, (∀ k, f k ≤ e k) ∧ ∑ k ∈ S, f k = n ∧ ∀ k, k ∉ S → f k = 0 := by sorry
