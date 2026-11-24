-- Prove2me | Theorems.Thm_GlobalTheory_HermClass_exists_finite_classes
-- name    : GlobalTheory.HermClass.exists_finite_classes
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:19:20.994002+00:00
-- url     : https://prove2.me/theorems/ca0ce123-e1fe-43e0-a529-093ed782c700
-- title:
--   Herm Class: exists finite classes
-- statement:
--   The Herm Class construction uses the exists finite classes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsFiniteRepresentatives.lean#L57-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsFiniteRepresentatives.lean#L57-L189

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteOrthogonalLengths_208b36ca428fb8e7
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteRepresentatives_c0b95eec68dc9003
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermClass
open Module Submodule NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.HermClass.exists_finite_classes {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (hs : ∀ x y, h y x = star (h x y))
    (hnd : ∀ y, (∀ x, h y x = 0) → y = 0) {N m : ℤ} (hN : N ≠ 0) (hm : m ≠ 0)
    {α : Type*} {ι : Type*} [Finite ι] (Λ : α → Submodule ℤ V) (t : α → ι → V)
    (hfg : ∀ a, (Λ a).FG) (hsp : ∀ a, span E (Λ a : Set V) = ⊤)
    (hO : ∀ a, ∀ c : E, IsIntegral ℤ c → ∀ x ∈ Λ a, c • x ∈ Λ a)
    (hint : ∀ a, ∀ x ∈ Λ a, ∀ y ∈ Λ a, IsIntegral ℤ (h x y))
    (hdual : ∀ a y, (∀ x ∈ Λ a, IsIntegral ℤ (h y x)) → (N : E) • y ∈ Λ a)
    (ht : ∀ a i, t a i ∈ Λ a) :
    ∃ S : Set α, S.Finite ∧ ∀ a, ∃ s ∈ S, ∃ γ : V ≃ₗ[E] V, (∀ x y, h (γ x) (γ y) = h x y) ∧
      (∀ x, x ∈ Λ a ↔ γ x ∈ Λ s) ∧ ∀ i, ∃ y ∈ Λ s, γ (t a i) - t s i = m • y := by sorry
