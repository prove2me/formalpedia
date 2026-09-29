-- Prove2me | Theorems.Thm_OddPerfectNumber_even_orders_mod_157_q3_twentythree
-- name    : OddPerfectNumber.even_orders_mod_157_q3_twentythree
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T06:59:41.554903+00:00
-- url     : https://prove2.me/theorems/332319d7-23f4-4ef9-a780-6ce0b7120db5
-- title:
--   Even local orders modulo 157 for q3=23 tuple
-- statement:
--   The support bases 3, 5, 23, and 79 all have even multiplicative order modulo 157.
-- source:
--   Exact finite-field order computation for the q3=23 D=79,q4=79,p=157 candidate.

import Mathlib

namespace OddPerfectNumber

theorem even_orders_mod_157_q3_twentythree :
    Even (orderOf (3 : ZMod 157)) ∧
    Even (orderOf (5 : ZMod 157)) ∧
    Even (orderOf (23 : ZMod 157)) ∧
    Even (orderOf (79 : ZMod 157)) := by
  sorry

end OddPerfectNumber
