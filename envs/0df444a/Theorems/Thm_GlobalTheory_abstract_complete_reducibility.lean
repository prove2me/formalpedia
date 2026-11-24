-- Prove2me | Theorems.Thm_GlobalTheory_abstract_complete_reducibility
-- name    : GlobalTheory.abstract_complete_reducibility
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:04:31.388819+00:00
-- url     : https://prove2.me/theorems/947347af-4669-432d-bbc0-8babcb5c0d4f
-- title:
--   Global Theory: abstract complete reducibility
-- statement:
--   The Global Theory construction uses the abstract complete reducibility property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/AbstractCompleteReducibility.lean#L28-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/AbstractCompleteReducibility.lean#L28-L142

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AbstractCompleteReducibility
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory

theorem GlobalTheory.abstract_complete_reducibility :
    ∀ {E : Type} [AddCommGroup E] [Module ℂ E] (P : Submodule ℂ E → Prop),
    (∀ s : Set (Submodule ℂ E), (∀ A ∈ s, P A) → P (sInf s)) →
    ∀ (N : Submodule ℂ E), P N → ∀ (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ), (∀ x ∈ N, x ≠ 0 → 0 < (b x x).re) →
    (∀ x ∈ N, ∀ y ∈ N, star (b x y) = b y x) →
    (∀ A : Submodule ℂ E, A ≤ N → P A → P (N ⊓ ⨅ a ∈ A, LinearMap.ker (b a))) →
    ∀ (e : E →ₗ[ℂ] E), (∀ A : Submodule ℂ E, A ≤ N → P A → ∀ x ∈ A, e x ∈ A) → (∀ x ∈ N, e (e x) = e x) →
    (∀ x ∈ N, ∀ y ∈ N, b (e x) y = b x (e y)) → FiniteDimensional ℂ (N.map e) →
    ∀ ψ ∈ N, e ψ = ψ →
    ψ ∈ ⨆ (A : Submodule ℂ E) (_ : A ≤ N ∧ P A ∧ A ≠ ⊥ ∧ ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A), A := by sorry
