-- Prove2me | Theorems.Thm_GlobalTheory_support_subgroup_odd_index
-- name    : GlobalTheory.support_subgroup_odd_index
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:52:06.550508+00:00
-- url     : https://prove2.me/theorems/215c5469-d524-4bfd-8908-24f405aabd71
-- title:
--   Global Theory: support subgroup odd index
-- statement:
--   The Global Theory construction uses the support subgroup odd index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsPrimeHomZmodOfNeTop.lean#L44-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsPrimeHomZmodOfNeTop.lean#L44-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsPrimeHomZmodOfNeTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.support_subgroup_odd_index :
    ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (S S₂ : Set X), S.Nonempty → (∀ a b, (a ∈ S ∧ b ∈ S) ↔ (a + b ∈ S₂ ∧ a - b ∈ S₂)) → (∀ x : X, ∃ z : X, x + (z + z) ∈ S₂) → S₂ = S ∧ ∃ Λ : AddSubgroup X, (Λ : Set X) = S ∧ (Λ = ⊤ ∨ ∃ l : ℕ, l.Prime ∧ Odd l ∧ ∃ f : X →+ ZMod l, f ≠ 0 ∧ ∀ x ∈ Λ, f x = 0) := by sorry
