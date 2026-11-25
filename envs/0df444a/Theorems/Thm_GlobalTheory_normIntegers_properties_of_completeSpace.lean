-- Prove2me | Theorems.Thm_GlobalTheory_normIntegers_properties_of_completeSpace
-- name    : GlobalTheory.normIntegers_properties_of_completeSpace
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:12:19.345638+00:00
-- url     : https://prove2.me/theorems/17a8e89a-90fd-43fb-953d-d73e57cf74ed
-- title:
--   Global Theory: norm Integers properties of complete Space
-- statement:
--   The Global Theory construction uses the norm Integers properties of complete Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L500-L528
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L500-L528

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

theorem GlobalTheory.normIntegers_properties_of_completeSpace (C : Type*) [NontriviallyNormedField C]
    [IsUltrametricDist C] [CompleteSpace C] :
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
        g.comp (algebraMap A _) = f → IsLocalHom g) := by sorry
