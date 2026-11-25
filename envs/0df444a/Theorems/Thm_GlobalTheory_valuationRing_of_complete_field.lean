-- Prove2me | Theorems.Thm_GlobalTheory_valuationRing_of_complete_field
-- name    : GlobalTheory.valuationRing_of_complete_field
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:51:26.479039+00:00
-- url     : https://prove2.me/theorems/31c47504-c1ff-4f08-b362-42170f321c9c
-- title:
--   Global Theory: valuation Ring of complete field
-- statement:
--   The Global Theory construction uses the valuation Ring of complete field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L530-L563
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L530-L563

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u

theorem GlobalTheory.valuationRing_of_complete_field :
    (∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C],
      (∀ w : normIntegers C, ‖(w : C)‖ < 1 → IsAdicComplete (Ideal.span {w}) (normIntegers C)) ∧
      (∀ J : Ideal (normIntegers C), J.FG → J.IsPrincipal) ∧
      (∀ J : Ideal (normIntegers C), J.FG → J ≤ IsLocalRing.maximalIdeal (normIntegers C) →
        J = ⊥ ∨ ∃ w : normIntegers C, 0 < ‖(w : C)‖ ∧ ‖(w : C)‖ < 1 ∧ J = Ideal.span {w}) ∧
      HenselianLocalRing (normIntegers C) ∧
      ringKrullDim (normIntegers C) = 1 ∧
      (IsAlgClosed C →
        (∀ (γ : (normIntegers C).ValueGroup) (n : ℕ), 0 < n → ∃ δ, δ ^ n = γ) ∧
        (∀ (x : C) (n : ℕ), 0 < n → ∃ y : C, ‖y‖ ^ n = ‖x‖) ∧
        IsAlgClosed (IsLocalRing.ResidueField (normIntegers C))) ∧
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
        (f : A →+* normIntegers C) [IsLocalHom f],
        (∃! g : AdicCompletion (IsLocalRing.maximalIdeal A) A →+* normIntegers C,
          g.comp (algebraMap A _) = f) ∧
        ∀ g : AdicCompletion (IsLocalRing.maximalIdeal A) A →+* normIntegers C,
          g.comp (algebraMap A _) = f → IsLocalHom g)) ∧
    (∀ (V K : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
      [Algebra V K] [IsFractionRing V K],
      (∀ a : V, a ≠ 0 → a ∈ IsLocalRing.maximalIdeal V → ∀ r : ℝ, 0 < r → r < 1 →
        ∃ (C : Type u) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C)
          (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : Algebra K C),
          (∀ x : K, ‖algebraMap K C x‖ ≤ 1 ↔ x ∈ (algebraMap V K).range) ∧
            ‖algebraMap K C (algebraMap V K a)‖ = r) ∧
      (∀ [CharZero K] (p : ℕ) [Fact p.Prime], (p : V) ∈ IsLocalRing.maximalIdeal V →
        ∃ (C : Type u) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C)
          (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : NormedAlgebra ℚ_[p] C) (_ : Algebra K C),
          ∀ x : K, ‖algebraMap K C x‖ ≤ 1 ↔ x ∈ (algebraMap V K).range)) := by sorry
