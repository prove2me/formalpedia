-- Prove2me | Theorems.Thm_GlobalTheory_pow_mem_range_includeRight_of_isPurelyInseparable
-- name    : GlobalTheory.pow_mem_range_includeRight_of_isPurelyInseparable
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:14:03.050164+00:00
-- url     : https://prove2.me/theorems/2c388fde-c756-4376-944d-50093cc4beee
-- title:
--   Global Theory: pow mem range include Right of is Purely Inseparable
-- statement:
--   The Global Theory construction uses the pow mem range include Right of is Purely Inseparable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdempotentTensorEqZeroOrOneOfIsPurelyInseparable.lean#L8-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdempotentTensorEqZeroOrOneOfIsPurelyInseparable.lean#L8-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowPowMemRangeIncludeRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdempotentTensorEqZeroOrOneOfIsPurelyInseparable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.pow_mem_range_includeRight_of_isPurelyInseparable (k K B : Type) [Field k] [Field K]
    [Algebra k K] [IsPurelyInseparable k K] [CommRing B] [Nontrivial B] [Algebra k B]
    (q : ℕ) [ExpChar k q] (z : K ⊗[k] B) :
    ∃ n : ℕ, z ^ q ^ n ∈
      (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B).range := by sorry
