-- Prove2me | Theorems.Thm_GlobalTheory_exists_etale_algHom_lift_of_smooth
-- name    : GlobalTheory.exists_etale_algHom_lift_of_smooth
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:31:13.760799+00:00
-- url     : https://prove2.me/theorems/13042d62-4615-43f6-99ba-d81e98b9cae7
-- title:
--   Global Theory: exists etale alg Hom lift of smooth
-- statement:
--   The Global Theory construction uses the exists etale alg Hom lift of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L224-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L224-L261

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open scoped TensorProduct
universe u
variable {R : Type*} {A B : Type u} {K : Type*} [CommRing R] [CommRing A] [CommRing B] [Field K]
  [Algebra R A] [Algebra R B] [Algebra R K] [IsLocalRing B] [Algebra B K] [IsScalarTower R B K]
  [Algebra (ResidueField B) K] [IsScalarTower B (ResidueField B) K]
  [Algebra.IsSeparable (ResidueField B) K]

theorem GlobalTheory.exists_etale_algHom_lift_of_smooth [Algebra.Smooth R A] (φ : A →ₐ[R] K) :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra B W) (_ : Algebra.Etale B W) (ψ : A →+* W)
      (ε : W →ₐ[B] K), ψ.comp (algebraMap R A) = (algebraMap B W).comp (algebraMap R B) ∧
        ∀ a, ε (ψ a) = φ a := by sorry
