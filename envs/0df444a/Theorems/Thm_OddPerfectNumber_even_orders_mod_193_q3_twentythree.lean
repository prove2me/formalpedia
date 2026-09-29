-- Prove2me | Theorems.Thm_OddPerfectNumber_even_orders_mod_193_q3_twentythree
-- name    : OddPerfectNumber.even_orders_mod_193_q3_twentythree
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T06:59:42.952638+00:00
-- url     : https://prove2.me/theorems/da67840f-06b8-47e5-9dee-0272bdaa1380
-- title:
--   Even local orders modulo 193 for q3=23 tuple
-- statement:
--   The support bases 3, 5, 23, and 97 all have even multiplicative order modulo 193.
-- source:
--   Exact finite-field order computation for the q3=23 D=97,q4=97,p=193 candidate.

import Mathlib

namespace OddPerfectNumber

theorem even_orders_mod_193_q3_twentythree :
    Even (orderOf (3 : ZMod 193)) ∧
    Even (orderOf (5 : ZMod 193)) ∧
    Even (orderOf (23 : ZMod 193)) ∧
    Even (orderOf (97 : ZMod 193)) := by
  sorry

end OddPerfectNumber
