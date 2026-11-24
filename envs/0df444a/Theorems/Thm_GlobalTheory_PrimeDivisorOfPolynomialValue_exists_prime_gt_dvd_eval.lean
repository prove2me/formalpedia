-- Prove2me | Theorems.Thm_GlobalTheory_PrimeDivisorOfPolynomialValue_exists_prime_gt_dvd_eval
-- name    : GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:34.450804+00:00
-- url     : https://prove2.me/theorems/28f9364f-3010-4787-a851-940f90e5a94f
-- title:
--   Prime Divisor Of Polynomial Value: exists prime gt dvd eval
-- statement:
--   The Prime Divisor Of Polynomial Value construction uses the exists prime gt dvd eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimeGtDvdEval.lean#L25-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimeGtDvdEval.lean#L25-L62

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

theorem GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval :
    ∀ (f : Polynomial ℤ), (0 : ℕ) < Polynomial.natDegree f → ∀ (n : ℕ),
      ∃ (p : ℕ), Nat.Prime p ∧ n < p ∧ ∃ (x : ℤ), (↑p : ℤ) ∣ Polynomial.eval x f := by sorry
