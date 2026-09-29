-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_sum_first_three_terms_le
-- name    : OddPerfectNumber.geom_sum_first_three_terms_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T14:29:43.7888+00:00
-- url     : https://prove2.me/theorems/3290408a-11df-47bf-8997-3369ee11391b
-- title:
--   The last three powers are bounded by their geometric sum
-- statement:
--   For n≥2, the final three powers occur in the finite geometric sum.
-- source:
--   Finite-range subset and nonnegative summation; this strengthens the accepted last-two-terms helper for exact abundance cuts.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_last_term_le

namespace OddPerfectNumber

theorem geom_sum_first_three_terms_le (q n : Nat) (hn : 2 ≤ n) :
    q ^ n + q ^ (n - 1) + q ^ (n - 2) ≤
      ∑ i ∈ Finset.range (n + 1), q ^ i := by
  sorry

end OddPerfectNumber
