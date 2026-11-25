-- Prove2me | Theorems.Thm_GlobalTheory_flat_of_surjective_cotangent
-- name    : GlobalTheory.flat_of_surjective_cotangent
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:52:19.429795+00:00
-- url     : https://prove2.me/theorems/3675c4be-4f6f-4050-a21a-286d74ac33ea
-- title:
--   Global Theory: flat of surjective cotangent
-- statement:
--   The Global Theory construction uses the flat of surjective cotangent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L405-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L405-L426

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
variable {A : Type*} [CommRing A]
variable {B : Type*} [CommRing B] {φ : A →+* B} {I : Ideal A} {J : Ideal B}
variable [IsNoetherianRing A] {φ : A →+* A}

theorem GlobalTheory.flat_of_surjective_cotangent {k : Type*} [CommRing k] [Algebra k A] [IsLocalRing A]
    (φ : A →ₐ[k] A) [IsLocalHom (φ : A →+* A)]
    (hle : maximalIdeal A ≤ (maximalIdeal A).comap φ)
    (h₀ : Function.Surjective (ResidueField.map (φ : A →+* A)))
    (h₁ : Function.Surjective (Ideal.mapCotangent _ _ φ hle)) :
    (∃ ψ : AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal A) A,
      (∀ n x, AdicCompletion.evalₐ _ n (ψ x) =
        Ideal.quotientMap (maximalIdeal A ^ n) (φ : A →+* A) (pow_le_comap_pow_of_le hle n)
          (AdicCompletion.evalₐ _ n x)) ∧
      ∀ a, ψ (algebraMap A _ a) = algebraMap A _ (φ a)) ∧ (φ : A →+* A).Flat := by sorry
