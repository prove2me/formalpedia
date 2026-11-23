-- Prove2me | Theorems.Thm_GlobalTheory_lTensor_comp_mulLeft_of_balanced
-- name    : GlobalTheory.lTensor_comp_mulLeft_of_balanced
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:14.738465+00:00
-- url     : https://prove2.me/theorems/e07a5d88-b70c-4a9c-b736-03a7670a235b
-- title:
--   Global Theory: l Tensor comp mul Left of balanced
-- statement:
--   The Global Theory construction uses the l Tensor comp mul Left of balanced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdTraceOfBalancedTensor.lean#L38-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdTraceOfBalancedTensor.lean#L38-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdTraceOfBalancedTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {O H : Type*} [CommRing O] [CommRing H] [Algebra O H]

theorem GlobalTheory.lTensor_comp_mulLeft_of_balanced {N : Type*} [AddCommGroup N] [Module O N]
    (Θ : H ⊗[O] H) (hΘ : ∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ)
    (α : H →ₗ[O] N) (h : H) :
    LinearMap.lTensor H (α ∘ₗ LinearMap.mulLeft O h) Θ = h • LinearMap.lTensor H α Θ := by sorry
