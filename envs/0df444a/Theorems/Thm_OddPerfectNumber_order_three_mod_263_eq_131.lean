-- Prove2me | Theorems.Thm_OddPerfectNumber_order_three_mod_263_eq_131
-- name    : OddPerfectNumber.order_three_mod_263_eq_131
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T16:36:25.357511+00:00
-- url     : https://prove2.me/theorems/94b79501-c8c6-4aeb-af6f-c78ce64322f8
-- title:
--   The order of 3 modulo 263 is 131
-- statement:
--   The residue class of 3 modulo 263 has multiplicative order 131.
-- source:
--   Exact finite order certificate for the D=75 q3=19 branch.

import Mathlib

namespace OddPerfectNumber

theorem order_three_mod_263_eq_131 :
    orderOf (3 : ZMod 263) = 131 := by
  sorry

end OddPerfectNumber
