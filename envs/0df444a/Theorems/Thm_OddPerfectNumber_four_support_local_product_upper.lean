-- Prove2me | Theorems.Thm_OddPerfectNumber_four_support_local_product_upper
-- name    : OddPerfectNumber.four_support_local_product_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T15:49:24.831567+00:00
-- url     : https://prove2.me/theorems/f289ef64-2573-408a-b99f-bd14c8ec5d77
-- title:
--   Four local sigma bounds multiply
-- statement:
--   Four local strict geometric-sum bounds multiply to the exact four-support upper bound 2880*(x1*x2*x3*x4) < 5005*(y1*y2*y3*y4).
-- source:
--   Algebraic product layer of the four-support k=1 abundancy certificate. The constants are 4*6*10*12 and 5*7*11*13.

import Mathlib

namespace OddPerfectNumber

theorem four_support_local_product_upper (x1 x2 x3 x4 y1 y2 y3 y4 : Nat)
    (h1 : 4 * x1 < 5 * y1)
    (h2 : 6 * x2 < 7 * y2)
    (h3 : 10 * x3 < 11 * y3)
    (h4 : 12 * x4 < 13 * y4) :
    2880 * (x1 * x2 * x3 * x4) < 5005 * (y1 * y2 * y3 * y4) := by
  sorry

end OddPerfectNumber
