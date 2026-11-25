-- Prove2me | Theorems.Thm_GlobalTheory_T_bijective_of_lTensor_bijective_of_flat_family
-- name    : GlobalTheory.T.bijective_of_lTensor_bijective_of_flat_family
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:26:48.743816+00:00
-- url     : https://prove2.me/theorems/291f9e1d-c3ab-4c96-9fbf-2f8c00bb8bf8
-- title:
--   T: bijective of l Tensor bijective of flat family
-- statement:
--   The T construction uses the bijective of l Tensor bijective of flat family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BijectiveOfLTensorFlatFamilyStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BijectiveOfLTensorFlatFamilyStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BijectiveOfLTensorFlatFamily
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BijectiveOfLTensorFlatFamilyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.bijective_of_lTensor_bijective_of_flat_family : ∀ (R : Type) [CommRing R] (N N' : Type) [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N'] (f : N →ₗ[R] N') (J : Type) (B : J → Type) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)], (∀ i, Module.Flat R (B i)) → (∀ m : Ideal R, m.IsMaximal → ∃ i, Ideal.map (algebraMap R (B i)) m ≠ ⊤) → (∀ i, Function.Bijective (LinearMap.lTensor (B i) f)) → Function.Bijective f := by sorry
