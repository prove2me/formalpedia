-- Prove2me | Theorems.Thm_GlobalTheory_HermClass_exists_finite_lengths
-- name    : GlobalTheory.HermClass.exists_finite_lengths
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:19:13.657017+00:00
-- url     : https://prove2.me/theorems/5e517b56-5bd6-4ca0-86b9-ffacb361fb78
-- title:
--   Herm Class: exists finite lengths
-- statement:
--   The Herm Class construction uses the exists finite lengths property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsFiniteOrthogonalLengths.lean#L10-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsFiniteOrthogonalLengths.lean#L10-L95

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteOrthogonalLengths_208b36ca428fb8e7
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

theorem GlobalTheory.HermClass.exists_finite_lengths (n : ℕ) (hn : n ≠ 0) {N : ℤ} (hN : N ≠ 0) :
    ∃ S : Set E, S.Finite ∧ (0 : E) ∉ S ∧
      ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V), finrank E V = n →
      (∀ x y, h y x = star (h x y)) → (∀ y, (∀ x, h y x = 0) → y = 0) →
      Λ.FG → span E (Λ : Set V) = ⊤ →
      (∀ a : E, IsIntegral ℤ a → ∀ x ∈ Λ, a • x ∈ Λ) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (h x y)) →
      (∀ y, (∀ x ∈ Λ, IsIntegral ℤ (h y x)) → (N : E) • y ∈ Λ) →
      ∃ v ∈ Λ, h v v ∈ S := by sorry
