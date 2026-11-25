-- Prove2me | Theorems.Thm_GlobalTheory_flat_endomorphism_and_local_criterion
-- name    : GlobalTheory.flat_endomorphism_and_local_criterion
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:45:46.446458+00:00
-- url     : https://prove2.me/theorems/ee2e7836-3d40-5f7e-9c42-c54fd05713d1
-- title:
--   Global Theory: flat endomorphism and local criterion
-- statement:
--   The Global Theory construction uses the flat endomorphism and local criterion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L543-L575
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L543-L575

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open IsLocalRing

theorem GlobalTheory.flat_endomorphism_and_local_criterion :
    (∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (φ : A →+* A) [IsLocalHom φ],
      Function.Surjective (ResidueField.map φ) →
      (∀ y ∈ maximalIdeal A, ∃ x ∈ maximalIdeal A, φ x - y ∈ maximalIdeal A ^ 2) →
      (∃ ψ : AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal A) A,
        (∀ (n : ℕ) (x : AdicCompletion (maximalIdeal A) A) (a : A),
          AdicCompletion.evalₐ _ n x = Ideal.Quotient.mk _ a →
            AdicCompletion.evalₐ _ n (ψ x) = Ideal.Quotient.mk _ (φ a)) ∧
        ∀ a, ψ (algebraMap A _ a) = algebraMap A _ (φ a)) ∧ φ.Flat) ∧
    (∀ (T A B : Type u) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing A]
      [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B] [Algebra T A] [Algebra T B]
      [IsLocalRing B] [IsLocalHom (algebraMap T B)] [Module.Flat T B] (φ : A →ₐ[T] B),
      (Algebra.TensorProduct.map (AlgHom.id T (ResidueField T)) φ :
        ResidueField T ⊗[T] A →+* ResidueField T ⊗[T] B).Flat → (φ : A →+* B).Flat) ∧
    (∀ (k K A B : Type u) [CommRing k] [CommRing K] [Algebra k K] [Module.FaithfullyFlat k K]
      [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] (φ : A →ₐ[k] B),
      (Algebra.TensorProduct.map (AlgHom.id k K) φ : K ⊗[k] A →+* K ⊗[k] B).Flat →
        (φ : A →+* B).Flat) ∧
    (∀ (T R : Type u) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing R]
      [IsDomain R] [IsDiscreteValuationRing R] [Algebra T R] [IsLocalHom (algebraMap T R)]
      (J : Ideal R), J ≠ ⊤ → Module.Flat T (R ⧸ J) → J = ⊥) := by sorry
