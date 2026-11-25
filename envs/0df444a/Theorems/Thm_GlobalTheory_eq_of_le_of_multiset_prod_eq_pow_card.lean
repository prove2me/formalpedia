-- Prove2me | Theorems.Thm_GlobalTheory_eq_of_le_of_multiset_prod_eq_pow_card
-- name    : GlobalTheory.eq_of_le_of_multiset_prod_eq_pow_card
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:54:50.89619+00:00
-- url     : https://prove2.me/theorems/757f93fa-4fe8-460c-a9fb-e5c0a166f6c5
-- title:
--   Global Theory: eq of le of multiset prod eq pow card
-- statement:
--   The Global Theory construction uses the eq of le of multiset prod eq pow card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PowSubSelfMemSpanOfSplitsCompletely.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PowSubSelfMemSpanOfSplitsCompletely.lean#L7-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowSubSelfMemSpanOfSplitsCompletely
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

theorem GlobalTheory.eq_of_le_of_multiset_prod_eq_pow_card {g : ℕ} (hg : 0 < g) (s : Multiset ℕ)
    (hle : ∀ a ∈ s, g ≤ a) (hprod : s.prod = g ^ s.card) : ∀ a ∈ s, a = g := by sorry
