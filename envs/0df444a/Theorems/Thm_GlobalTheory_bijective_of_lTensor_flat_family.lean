-- Prove2me | Theorems.Thm_GlobalTheory_bijective_of_lTensor_flat_family
-- name    : GlobalTheory.bijective_of_lTensor_flat_family
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:06:50.222148+00:00
-- url     : https://prove2.me/theorems/45fd2a51-bc45-4883-99f6-8b44cd305013
-- title:
--   Global Theory: bijective of l Tensor flat family
-- statement:
--   The Global Theory construction uses the bijective of l Tensor flat family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BijectiveOfLTensorFlatFamily.lean#L39-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BijectiveOfLTensorFlatFamily.lean#L39-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BijectiveOfLTensorFlatFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory

theorem GlobalTheory.bijective_of_lTensor_flat_family : ∀ (R : Type) [CommRing R] (N N' : Type) [AddCommGroup N]
    [Module R N] [AddCommGroup N'] [Module R N'] (f : N →ₗ[R] N') (J : Type) (B : J → Type)
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)], (∀ i, Module.Flat R (B i)) →
    (∀ m : Ideal R, m.IsMaximal → ∃ i, Ideal.map (algebraMap R (B i)) m ≠ ⊤) →
    (∀ i, Function.Bijective (LinearMap.lTensor (B i) f)) → Function.Bijective f := by sorry
