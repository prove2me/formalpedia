-- Prove2me | Theorems.Thm_GlobalTheory_IsLeftCoaction_isInternal
-- name    : GlobalTheory.IsLeftCoaction.isInternal
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:13.753347+00:00
-- url     : https://prove2.me/theorems/7c5d8fac-72ec-545e-b06a-35bfc74ab13c
-- title:
--   Is Left Coaction: is Internal
-- statement:
--   The Is Left Coaction construction uses the is Internal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TensorCoeffOfMemTorusWeightSpace.lean#L220-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TensorCoeffOfMemTorusWeightSpace.lean#L220-L226

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsLeftCoactionIffIsCoactionComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TensorCoeffOfMemTorusWeightSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra AddMonoidAlgebra DirectSum
open GlobalTheory
variable {R : Type*} [CommSemiring R] {X : Type*}
variable {M : Type*} [AddCommMonoid M] [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M']
variable [DecidableEq X]

theorem GlobalTheory.IsLeftCoaction.isInternal {ρ : M →ₗ[R] R[X] ⊗[R] M} (h : IsLeftCoaction ρ) :
    IsInternal fun x : X => LinearMap.eqLocus ρ (TensorProduct.mk R R[X] M (single x 1)) := by sorry
