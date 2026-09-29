-- Prove2me | Theorems.Thm_OddPerfectNumber_even_orders_mod_113_q4_593_599_601
-- name    : OddPerfectNumber.even_orders_mod_113_q4_593_599_601
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-14T19:57:53.988995+00:00
-- url     : https://prove2.me/theorems/a798ef44-5314-4085-8a56-5cf3552f086b
-- title:
--   Even q4 orders modulo 113 for the D=57 candidates
-- statement:
--   The three D=57 q3=19 fourth-prime candidates 593, 599, and 601 have even multiplicative order modulo 113.
-- source:
--   Exact finite-field computation of the three order parities; these certificates feed the accepted p=113 source obstruction.

import Mathlib

namespace OddPerfectNumber

theorem even_orders_mod_113_q4_593_599_601 :
    Even (orderOf (593 : ZMod 113)) ∧
      Even (orderOf (599 : ZMod 113)) ∧
      Even (orderOf (601 : ZMod 113)) := by
  sorry

end OddPerfectNumber
