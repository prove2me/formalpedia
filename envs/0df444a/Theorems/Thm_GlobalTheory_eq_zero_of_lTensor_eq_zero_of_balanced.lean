-- Prove2me | Theorems.Thm_GlobalTheory_eq_zero_of_lTensor_eq_zero_of_balanced
-- name    : GlobalTheory.eq_zero_of_lTensor_eq_zero_of_balanced
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:18:54.843388+00:00
-- url     : https://prove2.me/theorems/a244f797-5e16-4a3f-b53f-a6e630025d94
-- title:
--   Global Theory: eq zero of l Tensor eq zero of balanced
-- statement:
--   The Global Theory construction uses the eq zero of l Tensor eq zero of balanced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdTraceOfBalancedTensor.lean#L97-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdTraceOfBalancedTensor.lean#L97-L153

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

theorem GlobalTheory.eq_zero_of_lTensor_eq_zero_of_balanced [Module.Free O H] [Module.Finite O H]
    (Θ : H ⊗[O] H) (hΘ : ∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra O K]
    (hK : ∀ ga : H →ₐ[O] K, Algebra.TensorProduct.map (AlgHom.id O H) ga Θ ≠ 0)
    (α : H →ₗ[O] K) (hα : LinearMap.lTensor H α Θ = 0) : α = 0 := by sorry
