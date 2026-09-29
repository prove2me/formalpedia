-- Prove2me | Theorems.Thm_OddPerfectNumber_even_orders_mod_113_q4_599_601
-- name    : OddPerfectNumber.even_orders_mod_113_q4_599_601
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T20:07:20.259457+00:00
-- url     : https://prove2.me/theorems/0671a010-7173-4876-b883-fabaed413ccb
-- title:
--   Even q4 orders modulo 113 for q4=599 and q4=601
-- statement:
--   The q4=599 and q4=601 fourth-prime candidates have even multiplicative order modulo 113.
-- source:
--   Exact finite-field divisor-squeeze certificates for the two genuinely even q4 orders; q4=593 is intentionally excluded because its order is 7.

import Mathlib

namespace OddPerfectNumber

theorem even_orders_mod_113_q4_599_601 :
    Even (orderOf (599 : ZMod 113)) ∧
      Even (orderOf (601 : ZMod 113)) := by
  sorry

end OddPerfectNumber
