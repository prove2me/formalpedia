-- Prove2me | Theorems.Thm_OddPerfectNumber_even_orders_mod_449_q3_twentynine
-- name    : OddPerfectNumber.even_orders_mod_449_q3_twentynine
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T09:22:07.690042+00:00
-- url     : https://prove2.me/theorems/5613bbbc-904f-42f9-9c10-1322dee5ba24
-- title:
--   Even orders of the four q3=29 D=225 support bases modulo 449
-- statement:
--   The support bases 3, 5, 29, and 37 all have even multiplicative order modulo the Euler prime 449.
-- source:
--   Odd-part certificate using 449−1=2^6·7 and explicit non-unit seventh-power residues for all four bases.

import Mathlib

namespace OddPerfectNumber

theorem even_orders_mod_449_q3_twentynine : Even (orderOf (3 : ZMod 449)) ∧ Even (orderOf (5 : ZMod 449)) ∧ Even (orderOf (29 : ZMod 449)) ∧ Even (orderOf (37 : ZMod 449)) := by
  sorry

end OddPerfectNumber
