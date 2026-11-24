-- Prove2me | Theorems.Thm_GlobalTheory_isTorsionFree_ringOfIntegers_of_isTorsionFree_int
-- name    : GlobalTheory.isTorsionFree_ringOfIntegers_of_isTorsionFree_int
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:01:25.908096+00:00
-- url     : https://prove2.me/theorems/5d328dcf-ea98-4310-935c-d08102d4c097
-- title:
--   Global Theory: is Torsion Free ring Of Integers of is Torsion Free int
-- statement:
--   The Global Theory construction uses the is Torsion Free ring Of Integers of is Torsion Free int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsTorsionFreeRingOfIntegersOfIsTorsionFreeInt.lean#L6-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsTorsionFreeRingOfIntegersOfIsTorsionFreeInt.lean#L6-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsTorsionFreeRingOfIntegersOfIsTorsionFreeInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory

theorem GlobalTheory.isTorsionFree_ringOfIntegers_of_isTorsionFree_int (E : Type) [Field E] [NumberField E]
    (N : Type) [AddCommGroup N] [Module (𝓞 E) N] [Module.IsTorsionFree ℤ N] :
    Module.IsTorsionFree (𝓞 E) N := by sorry
