-- Prove2me | Theorems.Thm_GlobalTheory_invertible_of_faithfullyFlat_baseChange_tensor_int
-- name    : GlobalTheory.invertible_of_faithfullyFlat_baseChange_tensor_int
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:48:04.959441+00:00
-- url     : https://prove2.me/theorems/43d7b961-d4ff-4fff-a627-d5fca38f3764
-- title:
--   Global Theory: invertible of faithfully Flat base Change tensor int
-- statement:
--   The Global Theory construction uses the invertible of faithfully Flat base Change tensor int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvertibleOfFaithfullyFlatBaseChangeTensorInt.lean#L7-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvertibleOfFaithfullyFlatBaseChangeTensorInt.lean#L7-L138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueBaseChangeEqOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvertibleOfFaithfullyFlatBaseChangeTensorInt
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

theorem GlobalTheory.invertible_of_faithfullyFlat_baseChange_tensor_int :
    ∀ (R R' O : Type) [CommRing R] [CommRing R'] [Algebra R R'] [CommRing O] [Module.FaithfullyFlat R R'] (M : Type) [AddCommGroup M]
    [Module R M] [Module O M] [SMulCommClass R O M] (N : Type) [AddCommGroup N] [Module R' N] [Module O N]
    [SMulCommClass R' O N] (e : R' ⊗[R] M ≃ₗ[R'] N), (∀ (a : O) (m : M), e (1 ⊗ₜ (a • m)) = a • e (1 ⊗ₜ m)) →
    letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
    letI : Module (R' ⊗[ℤ] O) N := TensorProduct.Algebra.module
    Module.Invertible (R' ⊗[ℤ] O) N → Module.Invertible (R ⊗[ℤ] O) M := by sorry
