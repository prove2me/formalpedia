-- Prove2me | Theorems.Thm_GlobalTheory_sum_addChar_trace_mul_eq
-- name    : GlobalTheory.sum_addChar_trace_mul_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:55:21.730616+00:00
-- url     : https://prove2.me/theorems/bedca60a-4204-53a5-805e-da07981a450b
-- title:
--   Global Theory: sum add Char trace mul eq
-- statement:
--   The Global Theory construction uses the sum add Char trace mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixGaussSumMulDualEqCardPowSq.lean#L8-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixGaussSumMulDualEqCardPowSq.lean#L8-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixGaussSumSingularAndInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixGaussSumMulDualEqCardPowSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped TensorProduct Classical
open GlobalTheory

theorem GlobalTheory.sum_addChar_trace_mul_eq {k : Type} [Field k] [Fintype k] [DecidableEq k] {R : Type}
    [CommRing R] [IsDomain R] (ψ : AddChar k R) (hψ : ψ.IsPrimitive) {r : ℕ}
    (m : Matrix (Fin r) (Fin r) k) :
    ∑ a : Matrix (Fin r) (Fin r) k, ψ (trace (a * m)) =
      if m = 0 then (Fintype.card k : R) ^ (r ^ 2) else 0 := by sorry
