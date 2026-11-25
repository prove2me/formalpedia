-- Prove2me | Theorems.Thm_GlobalTheory_exists_cut_columns_bounded_width
-- name    : GlobalTheory.exists_cut_columns_bounded_width
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:34:12.12407+00:00
-- url     : https://prove2.me/theorems/03fd1afc-1fa9-417e-9fe5-b2f80e888914
-- title:
--   Global Theory: exists cut columns bounded width
-- statement:
--   The Global Theory construction uses the exists cut columns bounded width property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsCutIntoBoundedGroupsFinset.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsCutIntoBoundedGroupsFinset.lean#L82-L84

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

theorem GlobalTheory.exists_cut_columns_bounded_width : ∀ (K s B : ℕ) (e : ℕ → ℕ), ∑ k ∈ Finset.Icc 1 K, e k ≤ s * B → ∃ pc : Fin s → ℕ → ℕ, (∀ k ∈ Finset.Icc 1 K, ∑ u, pc u k = e k) ∧ (∀ u, ∑ k ∈ Finset.Icc 1 K, pc u k ≤ B) ∧ ∀ u k, k ∉ Finset.Icc 1 K → pc u k = 0 := by sorry
