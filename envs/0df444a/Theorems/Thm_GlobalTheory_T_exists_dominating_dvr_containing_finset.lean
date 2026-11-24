-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_dominating_dvr_containing_finset
-- name    : GlobalTheory.T.exists_dominating_dvr_containing_finset
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:33:57.340243+00:00
-- url     : https://prove2.me/theorems/08302bee-001f-4c19-bab1-5803442d365f
-- title:
--   T: exists dominating dvr containing finset
-- statement:
--   The T construction uses the exists dominating dvr containing finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDominatingDvrContainingFinsetStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDominatingDvrContainingFinsetStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDominatingDvrContainingFinset
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDominatingDvrContainingFinsetStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_dominating_dvr_containing_finset : ∀ (F : Type) [Field F] [CharZero F] (T' : Subring F), IsDiscreteValuationRing T' → ∀ (s : Finset F), (1 : F) ∈ Submodule.span T' (s : Set F) → (∀ x ∈ s, ∀ y ∈ s, x * y ∈ Submodule.span T' (s : Set F)) → ∃ T'' : Subring F, IsDiscreteValuationRing T'' ∧ T' ≤ T'' ∧ (∀ x ∈ s, x ∈ T'') ∧ (∀ x ∈ T', (∃ y ∈ T'', x * y = 1) → ∃ y ∈ T', x * y = 1) ∧ (∀ y ∈ T'', ∃ d ∈ T', d ≠ 0 ∧ d * y ∈ Submodule.span T' (s : Set F)) := by sorry
