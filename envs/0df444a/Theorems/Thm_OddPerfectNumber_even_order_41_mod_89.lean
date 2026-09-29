-- Prove2me | Theorems.Thm_OddPerfectNumber_even_order_41_mod_89
-- name    : OddPerfectNumber.even_order_41_mod_89
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T22:41:38.778134+00:00
-- url     : https://prove2.me/theorems/0fe0f8b0-b2f7-49b2-b31b-726a67d103cc
-- title:
--   Even order of 41 modulo 89
-- statement:
--   The fourth support base 41 has even multiplicative order modulo the Euler prime 89.
-- source:
--   Finite odd-part certificate using 89−1=2^3·11 and the nontrivial 11th power of 41 modulo 89.

import Mathlib

namespace OddPerfectNumber

theorem even_order_41_mod_89 : Even (orderOf (41 : ZMod 89)) := by
  sorry

end OddPerfectNumber
