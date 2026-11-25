-- Prove2me | Theorems.Thm_GlobalTheory_IsCoaction_comm_iff_mapsTo_torusWeightSpace
-- name    : GlobalTheory.IsCoaction.comm_iff_mapsTo_torusWeightSpace
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:21.20939+00:00
-- url     : https://prove2.me/theorems/cb2d2634-0b33-598c-aa91-d79df93aa63f
-- title:
--   Is Coaction: comm iff maps To torus Weight Space
-- statement:
--   The Is Coaction construction uses the comm iff maps To torus Weight Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TensorCoeffOfMemTorusWeightSpace.lean#L206-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TensorCoeffOfMemTorusWeightSpace.lean#L206-L218

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
omit [DecidableEq X]

theorem GlobalTheory.IsCoaction.comm_iff_mapsTo_torusWeightSpace {ρ : M →ₗ[R] M ⊗[R] R[X]} (h : IsCoaction ρ)
    (ρ' : M' →ₗ[R] M' ⊗[R] R[X]) (f : M →ₗ[R] M') :
    (∀ m, ρ' (f m) = f.rTensor R[X] (ρ m)) ↔
      ∀ x, ∀ m ∈ torusWeightSpace ρ x, f m ∈ torusWeightSpace ρ' x := by sorry
