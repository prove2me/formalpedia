-- Prove2me | Theorems.Thm_GlobalTheory_exists_hyperbolic_completion
-- name    : GlobalTheory.exists_hyperbolic_completion
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:32:16.655875+00:00
-- url     : https://prove2.me/theorems/5904a3bf-c532-41a8-b156-c1c3fca194c8
-- title:
--   Global Theory: exists hyperbolic completion
-- statement:
--   The Global Theory construction uses the exists hyperbolic completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsHyperbolicCompletion.lean#L9-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsHyperbolicCompletion.lean#L9-L119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsHyperbolicCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module
open Module

theorem GlobalTheory.exists_hyperbolic_completion :
    ∀ (E V : Type) [Field E] [CharZero E] [StarRing E] [AddCommGroup V] [Module E V] [FiniteDimensional E V] (h : V →ₗ⋆[E] V →ₗ[E] E), h.IsSymm → h.Nondegenerate → ∀ (W : Submodule E V), (∀ x ∈ W, (∀ y ∈ W, h x y = 0) → x = 0) → ∀ (i : ℕ) (e : Fin i → V), LinearIndependent E e → (∀ a b, h (e a) (e b) = 0) → (∀ a, ∀ x ∈ W, h x (e a) = 0) → Module.finrank E W + 2 * i = Module.finrank E V → ∃ f : Fin i → V, (∀ a b, h (f a) (f b) = 0) ∧ (∀ a b, h (f a) (e b) = if a = b then 1 else 0) ∧ (∀ a, ∀ x ∈ W, h x (f a) = 0) ∧ W ⊔ Submodule.span E (Set.range e ∪ Set.range f) = ⊤ := by sorry
