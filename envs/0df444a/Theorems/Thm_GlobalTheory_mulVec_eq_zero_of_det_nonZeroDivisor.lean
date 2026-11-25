-- Prove2me | Theorems.Thm_GlobalTheory_mulVec_eq_zero_of_det_nonZeroDivisor
-- name    : GlobalTheory.mulVec_eq_zero_of_det_nonZeroDivisor
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:43:55.446365+00:00
-- url     : https://prove2.me/theorems/a265747a-0e65-4d12-9442-c180474796c7
-- title:
--   Global Theory: mul Vec eq zero of det non Zero Divisor
-- statement:
--   The Global Theory construction uses the mul Vec eq zero of det non Zero Divisor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TwistedTraceEquivariantAndInjectiveOfGroupDet.lean#L8-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TwistedTraceEquivariantAndInjectiveOfGroupDet.lean#L8-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwistedTraceEquivariantAndInjectiveOfGroupDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Matrix
open Polynomial
open GlobalTheory

theorem GlobalTheory.mulVec_eq_zero_of_det_nonZeroDivisor {n R : Type} [Fintype n] [DecidableEq n]
    [CommRing R] (A : Matrix n n R) (hA : A.det ∈ nonZeroDivisors R) (v : n → R)
    (hv : A *ᵥ v = 0) : v = 0 := by sorry
