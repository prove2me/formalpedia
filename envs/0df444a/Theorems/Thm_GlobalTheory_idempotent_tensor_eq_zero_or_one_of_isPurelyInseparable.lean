-- Prove2me | Theorems.Thm_GlobalTheory_idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable
-- name    : GlobalTheory.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:55:13.238796+00:00
-- url     : https://prove2.me/theorems/e40c7c73-1880-4fca-8d8f-02756d7d0ee5
-- title:
--   Global Theory: idempotent tensor eq zero or one of is Purely Inseparable
-- statement:
--   The Global Theory construction uses the idempotent tensor eq zero or one of is Purely Inseparable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdempotentTensorEqZeroOrOneOfIsPurelyInseparable.lean#L21-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdempotentTensorEqZeroOrOneOfIsPurelyInseparable.lean#L21-L43

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

theorem GlobalTheory.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable (k K B : Type) [Field k] [Field K]
    [Algebra k K] [IsPurelyInseparable k K] [CommRing B] [IsLocalRing B] [Algebra k B]
    (e : K ⊗[k] B) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by sorry
