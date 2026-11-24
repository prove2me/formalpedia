-- Prove2me | Theorems.Thm_GlobalTheory_contractRight_trace
-- name    : GlobalTheory.contractRight_trace
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:14:45.429301+00:00
-- url     : https://prove2.me/theorems/cf6fdf14-c243-46cf-a817-5c40fbd8e357
-- title:
--   Global Theory: contract Right trace
-- statement:
--   The Global Theory construction uses the contract Right trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdTraceOfBalancedTensor.lean#L77-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdTraceOfBalancedTensor.lean#L77-L95

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

theorem GlobalTheory.contractRight_trace {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι O H)
    (Θ : H ⊗[O] H) (hΘ : ∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ) :
    contractRight Θ (Algebra.trace O H) = Algebra.TensorProduct.lmul' O Θ := by sorry
