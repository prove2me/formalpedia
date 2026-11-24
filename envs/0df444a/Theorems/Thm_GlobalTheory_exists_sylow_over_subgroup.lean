-- Prove2me | Theorems.Thm_GlobalTheory_exists_sylow_over_subgroup
-- name    : GlobalTheory.exists_sylow_over_subgroup
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:42:21.936624+00:00
-- url     : https://prove2.me/theorems/ed5d883a-969d-461b-b7f5-8b834503d76e
-- title:
--   Global Theory: exists sylow over subgroup
-- statement:
--   The Global Theory construction uses the exists sylow over subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsSylowOverSubgroup.lean#L5-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsSylowOverSubgroup.lean#L5-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsSylowOverSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_sylow_over_subgroup (G : Type) [Group G] [Finite G] (C : Subgroup G) (p : ℕ)
    (hp : p.Prime) :
    ∃ H : Subgroup G, C ≤ H ∧ (∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C) ∧
      (∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ C) ∧
      ∀ N : Subgroup G, (∀ g : G, g ∈ N ↔ ∀ c ∈ C, g * c * g⁻¹ ∈ C) → ¬ p ∣ H.relIndex N := by sorry
