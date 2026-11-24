-- Prove2me | Theorems.Thm_GlobalTheory_exists_algHom_lift_of_isStandardEtale
-- name    : GlobalTheory.exists_algHom_lift_of_isStandardEtale
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:29:07.453821+00:00
-- url     : https://prove2.me/theorems/9383cd9a-8261-4794-add9-bbbcffd1b60b
-- title:
--   Global Theory: exists alg Hom lift of is Standard Etale
-- statement:
--   The Global Theory construction uses the exists alg Hom lift of is Standard Etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L37-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L37-L58

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
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

theorem GlobalTheory.exists_algHom_lift_of_isStandardEtale [Algebra.IsStandardEtale R A] (I : Ideal B)
    [HenselianRing B I] (π : B →ₐ[R] C) (hπ : Function.Surjective π) (hI : ∀ b, b ∈ I ↔ π b = 0)
    (φ : A →ₐ[R] C) : ∃ ψ : A →ₐ[R] B, π.comp ψ = φ := by sorry
