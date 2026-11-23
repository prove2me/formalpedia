-- Prove2me | Theorems.Thm_GlobalTheory_IsCoaction_rid_counit
-- name    : GlobalTheory.IsCoaction.rid_counit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:50:21.492617+00:00
-- url     : https://prove2.me/theorems/4d9ae80f-1118-4d6e-96c3-4ef927ef76f4
-- title:
--   Is Coaction: rid counit
-- statement:
--   The Is Coaction construction uses the rid counit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsLeftCoactionIffIsCoactionComm.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsLeftCoactionIffIsCoactionComm.lean#L43-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsLeftCoactionIffIsCoactionComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra
open GlobalTheory
variable {R : Type*} [CommSemiring R] {C : Type*} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {M : Type*} [AddCommMonoid M] [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M']

theorem GlobalTheory.IsCoaction.rid_counit {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ) (m : M) :
    TensorProduct.rid R M ((Coalgebra.counit : C →ₗ[R] R).lTensor M (ρ m)) = m := by sorry
