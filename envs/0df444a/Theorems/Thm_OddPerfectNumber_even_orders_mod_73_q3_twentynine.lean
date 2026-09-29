-- Prove2me | Theorems.Thm_OddPerfectNumber_even_orders_mod_73_q3_twentynine
-- name    : OddPerfectNumber.even_orders_mod_73_q3_twentynine
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T06:45:53.94796+00:00
-- url     : https://prove2.me/theorems/ac9c5093-c984-48ae-a3c7-f5765d598aed
-- title:
--   Even orders of 3, 5, and 29 modulo 73
-- statement:
--   In the q3=29 D=37, p=73 case, the fixed support bases 3, 5, and 29 all have even multiplicative order modulo 73.
-- source:
--   Odd-part certificate: 73−1=2^3·9; explicit ninth-power residues rule out odd order for each fixed base.

import Mathlib

namespace OddPerfectNumber

theorem even_orders_mod_73_q3_twentynine :
    Even (orderOf (3 : ZMod 73)) ∧
      Even (orderOf (5 : ZMod 73)) ∧
      Even (orderOf (29 : ZMod 73)) := by
  sorry

end OddPerfectNumber
