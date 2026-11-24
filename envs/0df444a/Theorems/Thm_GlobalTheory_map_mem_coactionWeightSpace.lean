-- Prove2me | Theorems.Thm_GlobalTheory_map_mem_coactionWeightSpace
-- name    : GlobalTheory.map_mem_coactionWeightSpace
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:09:31.690122+00:00
-- url     : https://prove2.me/theorems/13a50ac1-f03f-4097-8077-fc4d6898c5e0
-- title:
--   Global Theory: map mem coaction Weight Space
-- statement:
--   The Global Theory construction uses the map mem coaction Weight Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsLeftCoactionIffIsCoactionComm.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsLeftCoactionIffIsCoactionComm.lean#L108-L112

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
omit [Coalgebra R C]

theorem GlobalTheory.map_mem_coactionWeightSpace {ρ : M →ₗ[R] M ⊗[R] C} {ρ' : M' →ₗ[R] M' ⊗[R] C}
    {f : M →ₗ[R] M'} (hf : ∀ m, ρ' (f m) = f.rTensor C (ρ m)) {g : C} {m : M}
    (hm : m ∈ coactionWeightSpace ρ g) : f m ∈ coactionWeightSpace ρ' g := by sorry
