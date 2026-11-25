-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_mul_of_bounded_at_points
-- name    : GlobalTheory.isIntegral_mul_of_bounded_at_points
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:55.811153+00:00
-- url     : https://prove2.me/theorems/572c8be9-b0a8-4b47-bb6c-609d11770c42
-- title:
--   Global Theory: is Integral mul of bounded at points
-- statement:
--   The Global Theory construction uses the is Integral mul of bounded at points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IsIntegralCoeffZeroMulOfAevalInv.lean#L9-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IsIntegralCoeffZeroMulOfAevalInv.lean#L9-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsIntegralCoeffZeroMulOfAevalInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial
open Polynomial

theorem GlobalTheory.isIntegral_mul_of_bounded_at_points :
    ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [CharZero O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → (∀ (B : Type) [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B], Function.Injective (algebraMap O B) → ∀ I : Ideal B, I ≠ ⊤ → Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I → ∀ e : B, e ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O' V) (_ : Module.Finite O' V) (φ : B →+* V), φ.comp (algebraMap O B) = (algebraMap O' V).comp (algebraMap O O') ∧ φ e ≠ 0 ∧ ∀ x ∈ I, φ x ∈ IsLocalRing.maximalIdeal V) → ∀ (A Ω : Type) [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω], Function.Injective (algebraMap O A) → ∀ (e : A), e ≠ 0 → ∀ f : Ω, (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O' V] [Module.Finite O' V] (φ : A →+* V), φ.comp (algebraMap O A) = (algebraMap O' V).comp (algebraMap O O') → φ e ≠ 0 → ∀ a b : A, f * algebraMap A Ω b = algebraMap A Ω a → φ b ≠ 0 → φ b ∣ φ a) → ∃ s : A, s - 1 ∈ Ideal.map (algebraMap O A) (IsLocalRing.maximalIdeal O) ∧ IsIntegral A (algebraMap A Ω s * f) := by sorry
