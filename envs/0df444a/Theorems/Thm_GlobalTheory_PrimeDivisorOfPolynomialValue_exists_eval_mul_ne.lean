-- Prove2me | Theorems.Thm_GlobalTheory_PrimeDivisorOfPolynomialValue_exists_eval_mul_ne
-- name    : GlobalTheory.PrimeDivisorOfPolynomialValue.exists_eval_mul_ne
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:53:44.653954+00:00
-- url     : https://prove2.me/theorems/1744b8de-e510-4d8b-b04e-b2d6dbe91700
-- title:
--   Prime Divisor Of Polynomial Value: exists eval mul ne
-- statement:
--   The Prime Divisor Of Polynomial Value construction uses the exists eval mul ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimeGtDvdEval.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimeGtDvdEval.lean#L7-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimeGtDvdEval
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PrimeDivisorOfPolynomialValue
open Polynomial

theorem GlobalTheory.PrimeDivisorOfPolynomialValue.exists_eval_mul_ne (f : ℤ[X]) (hf : 0 < f.natDegree) (c a : ℤ) (ha : a ≠ 0) :
    ∃ k : ℤ, f.eval (a * k) ≠ c ∧ f.eval (a * k) ≠ -c := by sorry
