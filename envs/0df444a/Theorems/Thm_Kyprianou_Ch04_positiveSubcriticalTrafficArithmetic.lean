-- Prove2me | Theorems.Thm_Kyprianou_Ch04_positiveSubcriticalTrafficArithmetic
-- name    : Kyprianou.Ch04.positiveSubcriticalTrafficArithmetic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:27:39.532488+00:00
-- url     : https://prove2.me/theorems/a86ec08d-19e3-5862-a9ac-e0aa68dc2bc7
-- title:
--   A traffic intensity strictly between zero and one implies a positive finite mean strictly smaller than the drift.
-- statement:
--   A traffic intensity strictly between zero and one implies a positive finite mean strictly smaller than the drift.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10

import Mathlib
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.positiveSubcriticalTrafficArithmetic (M : ENNReal) (d : ℝ) (hd : 0 < d)
    (hr0 : 0 < M / ENNReal.ofReal d) (hr1 : M / ENNReal.ofReal d < 1) :
    M ≠ ⊤ ∧ M ≠ 0 ∧ M.toReal < d := by
  sorry
