-- Prove2me | Theorems.Thm_GlobalTheory_KuennethOne_mem_range_rTensor_of_forall_dual
-- name    : GlobalTheory.KuennethOne.mem_range_rTensor_of_forall_dual
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:56:07.573398+00:00
-- url     : https://prove2.me/theorems/1560ae56-62df-4880-a942-287e4bdd3d36
-- title:
--   Kuenneth One: mem range r Tensor of forall dual
-- statement:
--   The Kuenneth One construction uses the mem range r Tensor of forall dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeRTensorOfForallDual.lean#L8-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeRTensorOfForallDual.lean#L8-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitsOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace TensorProduct
open GlobalTheory GlobalTheory.KuennethOne

theorem GlobalTheory.KuennethOne.mem_range_rTensor_of_forall_dual {R C₀ C₁ B : Type} [CommRing R] (hR : IsField R)
    [AddCommGroup C₀] [Module R C₀] [AddCommGroup C₁] [Module R C₁] [AddCommGroup B] [Module R B]
    (δ : C₀ →ₗ[R] C₁) (z : C₁ ⊗[R] B)
    (h : ∀ l : C₁ →ₗ[R] R, l ∘ₗ δ = 0 → TensorProduct.lid R B (l.rTensor B z) = 0) :
    ∃ y, δ.rTensor B y = z := by sorry
