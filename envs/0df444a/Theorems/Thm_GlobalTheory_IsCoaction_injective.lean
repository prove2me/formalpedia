-- Prove2me | Theorems.Thm_GlobalTheory_IsCoaction_injective
-- name    : GlobalTheory.IsCoaction.injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:53.000862+00:00
-- url     : https://prove2.me/theorems/d5bdef32-a00e-4dcf-8bd1-83b7541d06e0
-- title:
--   Is Coaction: injective
-- statement:
--   The Is Coaction construction uses the injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsLeftCoactionIffIsCoactionComm.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsLeftCoactionIffIsCoactionComm.lean#L47-L50

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

theorem GlobalTheory.IsCoaction.injective {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ) : Function.Injective ρ := by sorry
