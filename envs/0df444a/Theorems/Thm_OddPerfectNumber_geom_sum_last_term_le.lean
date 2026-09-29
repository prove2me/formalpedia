-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_sum_last_term_le
-- name    : OddPerfectNumber.geom_sum_last_term_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T02:44:39.689197+00:00
-- url     : https://prove2.me/theorems/ff577d9a-c08f-46c8-94cf-07ef2392261d
-- title:
--   The last power is bounded by its geometric sum
-- statement:
--   Every finite geometric sum contains its final power as a summand.
-- source:
--   Elementary reusable summand bound for finite abundance certificates.

import Mathlib

namespace OddPerfectNumber

theorem geom_sum_last_term_le (q e : Nat) :
    q ^ e ≤ ∑ i ∈ Finset.range (e + 1), q ^ i := by
  sorry

end OddPerfectNumber
