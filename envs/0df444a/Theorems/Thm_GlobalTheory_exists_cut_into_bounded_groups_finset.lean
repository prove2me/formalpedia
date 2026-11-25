-- Prove2me | Theorems.Thm_GlobalTheory_exists_cut_into_bounded_groups_finset
-- name    : GlobalTheory.exists_cut_into_bounded_groups_finset
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:26:56.12782+00:00
-- url     : https://prove2.me/theorems/03efa172-fa63-4ab3-b940-9f95f74e4fc1
-- title:
--   Global Theory: exists cut into bounded groups finset
-- statement:
--   The Global Theory construction uses the exists cut into bounded groups finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsCutIntoBoundedGroupsFinset.lean#L40-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsCutIntoBoundedGroupsFinset.lean#L40-L80

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

theorem GlobalTheory.exists_cut_into_bounded_groups_finset (S : Finset ℕ) (B : ℕ) :
    ∀ (s : ℕ) (e : ℕ → ℕ), ∑ k ∈ S, e k ≤ s * B →
      ∃ pc : Fin s → ℕ → ℕ, (∀ k ∈ S, ∑ u, pc u k = e k) ∧ (∀ u, ∑ k ∈ S, pc u k ≤ B) ∧
        ∀ u k, k ∉ S → pc u k = 0 := by sorry
