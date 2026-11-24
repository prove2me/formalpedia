-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_subgroup_ge_normalizing_not_dvd_relIndex
-- name    : GlobalTheory.T.exists_subgroup_ge_normalizing_not_dvd_relIndex
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:38:13.936192+00:00
-- url     : https://prove2.me/theorems/0f88033f-6b5f-4102-b8a9-84e4e161631a
-- title:
--   T: exists subgroup ge normalizing not dvd rel Index
-- statement:
--   The T construction uses the exists subgroup ge normalizing not dvd rel Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsSylowOverSubgroupStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsSylowOverSubgroupStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsSylowOverSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsSylowOverSubgroupStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_subgroup_ge_normalizing_not_dvd_relIndex : ∀ (G : Type) [Group G] [Finite G] (C : Subgroup G) (p : ℕ), p.Prime → ∃ H : Subgroup G, C ≤ H ∧ (∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C) ∧ (∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ C) ∧ ∀ N : Subgroup G, (∀ g : G, g ∈ N ↔ ∀ c ∈ C, g * c * g⁻¹ ∈ C) → ¬ p ∣ H.relIndex N := by sorry
