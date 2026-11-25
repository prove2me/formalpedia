-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_formal_inverse_function_theorem
-- name    : GlobalTheory.FormalInv.formal_inverse_function_theorem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:05:28.644841+00:00
-- url     : https://prove2.me/theorems/42325517-6046-4951-b910-aec51ea18685
-- title:
--   Formal Inv: formal inverse function theorem
-- statement:
--   The Formal Inv construction uses the formal inverse function theorem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L670-L712
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L670-L712

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries Finsupp
noncomputable section
open GlobalTheory GlobalTheory.FormalInv
variable {σ τ υ ι : Type*} {R : Type*} [CommRing R]

theorem GlobalTheory.FormalInv.formal_inverse_function_theorem :
    (∀ (R : Type) [CommRing R] (n : ℕ) (u : Fin n → MvPowerSeries (Fin n) R),
      (∀ i, constantCoeff (u i) = 0) →
      IsUnit (Matrix.of fun i j => coeff (single j 1) (u i) : Matrix (Fin n) (Fin n) R) →
      ∃! v : Fin n → MvPowerSeries (Fin n) R, (∀ i, constantCoeff (v i) = 0) ∧
        (∀ i, (u i).subst v = X i) ∧ ∀ i, (v i).subst u = X i) ∧
    (∀ (C : Type) [CommRing C] (S : Subring C) (g n m : ℕ)
      (l : Fin n → MvPowerSeries (Fin n) C) (l' : Fin m → MvPowerSeries (Fin m) C),
      (∀ i, (2 : ℕ∞) ≤ (l i - X i).order) → (∀ j, (2 : ℕ∞) ≤ (l' j - X j).order) →
      (∀ i (d : Fin n →₀ ℕ), d.degree < g → coeff d (l i) ∈ S) →
      (∀ j (d : Fin m →₀ ℕ), d.degree < g → coeff d (l' j) ∈ S) →
      ∃ (e : Fin n → MvPowerSeries (Fin n) C) (e' : Fin m → MvPowerSeries (Fin m) C),
        ((∀ i, (2 : ℕ∞) ≤ (e i - X i).order) ∧
          (∀ i, (l i).subst e = X i) ∧ (∀ i, (e i).subst l = X i) ∧
          ∀ i (d : Fin n →₀ ℕ), d.degree < g → coeff d (e i) ∈ S) ∧
        ((∀ j, (2 : ℕ∞) ≤ (e' j - X j).order) ∧
          (∀ j, (l' j).subst e' = X j) ∧ (∀ j, (e' j).subst l' = X j) ∧
          ∀ j (d : Fin m →₀ ℕ), d.degree < g → coeff d (e' j) ∈ S) ∧
        (∀ u : MvPowerSeries (Fin n ⊕ Fin m) S, ∀ (α : Fin n →₀ ℕ) (β : Fin m →₀ ℕ),
          α.degree < g → β.degree < g →
          coeff (α.sumElim β) ((MvPowerSeries.map S.subtype u).subst (sumFamily e e')) ∈ S) ∧
        (∀ v : MvPowerSeries (Fin n ⊕ Fin m) C,
          (∀ (α : Fin n →₀ ℕ) (β : Fin m →₀ ℕ), α.degree < g → β.degree < g →
            coeff (α.sumElim β) v ∈ S) →
          ∀ (α : Fin n →₀ ℕ) (β : Fin m →₀ ℕ), α.degree < g → β.degree < g →
            coeff (α.sumElim β) (v.subst (sumFamily l l')) ∈ S)) := by sorry
