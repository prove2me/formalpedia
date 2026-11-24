-- Prove2me | Theorems.Thm_GlobalTheory_TwoSidedShift_mem_pow_span_iff
-- name    : GlobalTheory.TwoSidedShift.mem_pow_span_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:16:43.174369+00:00
-- url     : https://prove2.me/theorems/41cee169-5418-40c1-a2f3-329194a8f8c2
-- title:
--   Two Sided Shift: mem pow span iff
-- statement:
--   The Two Sided Shift construction uses the mem pow span iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwoSidedShiftSeriesHasSum.lean#L6-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwoSidedShiftSeriesHasSum.lean#L6-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwoSidedShiftSeriesHasSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TwoSidedShift

theorem GlobalTheory.TwoSidedShift.mem_pow_span_iff (l : ℕ) (A : Type) [CommRing A] (n : ℕ) (x : A) :
    x ∈ ((Ideal.span {(l : A)}) ^ n • ⊤ : Submodule A A) ↔ (l : A) ^ n ∣ x := by sorry
