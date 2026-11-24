-- Prove2me | Theorems.Thm_GlobalTheory_ShiftMemPowOfMulMemPow_exists_shift_mem_pow_of_mul_mem_pow
-- name    : GlobalTheory.ShiftMemPowOfMulMemPow.exists_shift_mem_pow_of_mul_mem_pow
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:11:14.097794+00:00
-- url     : https://prove2.me/theorems/32298008-65a7-4fbf-b01d-8007e151a328
-- title:
--   Shift Mem Pow Of Mul Mem Pow: exists shift mem pow of mul mem pow
-- statement:
--   The Shift Mem Pow Of Mul Mem Pow construction uses the exists shift mem pow of mul mem pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsShiftMemPowOfMulMemPow.lean#L5-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsShiftMemPowOfMulMemPow.lean#L5-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsShiftMemPowOfMulMemPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ShiftMemPowOfMulMemPow

theorem GlobalTheory.ShiftMemPowOfMulMemPow.exists_shift_mem_pow_of_mul_mem_pow {R : Type} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (I : Ideal R) {r : R} (hr : r ≠ 0) :
    ∃ c : ℕ, ∀ (n : ℕ) (x : R), r * x ∈ I ^ (n + c) → x ∈ I ^ n := by sorry
