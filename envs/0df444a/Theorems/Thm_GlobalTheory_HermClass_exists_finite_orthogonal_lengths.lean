-- Prove2me | Theorems.Thm_GlobalTheory_HermClass_exists_finite_orthogonal_lengths
-- name    : GlobalTheory.HermClass.exists_finite_orthogonal_lengths
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:17:49.684046+00:00
-- url     : https://prove2.me/theorems/4fd2e079-ff26-4d7b-b1de-b8a9d7297d08
-- title:
--   Herm Class: exists finite orthogonal lengths
-- statement:
--   The Herm Class construction uses the exists finite orthogonal lengths property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsFiniteOrthogonalLengths.lean#L97-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsFiniteOrthogonalLengths.lean#L97-L193

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

theorem GlobalTheory.HermClass.exists_finite_orthogonal_lengths (n : ℕ) : ∀ {N : ℤ}, N ≠ 0 →
    ∃ S : Set E, S.Finite ∧ (0 : E) ∉ S ∧
      ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V), finrank E V = n →
      (∀ x y, h y x = star (h x y)) → (∀ y, (∀ x, h y x = 0) → y = 0) →
      Λ.FG → span E (Λ : Set V) = ⊤ →
      (∀ a : E, IsIntegral ℤ a → ∀ x ∈ Λ, a • x ∈ Λ) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (h x y)) →
      (∀ y, (∀ x ∈ Λ, IsIntegral ℤ (h y x)) → (N : E) • y ∈ Λ) →
      ∃ v : Fin n → V, (∀ i, v i ∈ Λ) ∧ (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧
        ∀ i, h (v i) (v i) ∈ S := by sorry
