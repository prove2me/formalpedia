-- Prove2me | Theorems.Thm_OddPerfectNumber_sigma_nineteen_square_value
-- name    : OddPerfectNumber.sigma_nineteen_square_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T19:06:50.093484+00:00
-- url     : https://prove2.me/theorems/1a53f50c-7f4c-44f4-9952-84d5d5e47061
-- title:
--   Exact local sigma value for 19 squared
-- statement:
--   The local divisor sum for 19 squared is 1+19+19^2=381=3*127.
-- source:
--   Exact arithmetic certificate for the q2=5, q3=19 finite-support branch.

import Mathlib

namespace OddPerfectNumber

theorem sigma_nineteen_square_value :
    (∑ i ∈ Finset.range (2 + 1), 19 ^ i) = 3 * 127 := by sorry

end OddPerfectNumber
