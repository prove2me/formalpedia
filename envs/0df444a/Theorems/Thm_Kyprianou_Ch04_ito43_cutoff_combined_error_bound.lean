-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_combined_error_bound
-- name    : Kyprianou.Ch04.ito43_cutoff_combined_error_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:35:37.906789+00:00
-- url     : https://prove2.me/theorems/7ecc4946-ea74-472d-b47b-81a922dad0af
-- title:
--   Combine complementary jump and grid errors
-- statement:
--   The total complementary cutoff error is bounded by the sum of the jump and grid energy bounds.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
set_option autoImplicit false

/-- Combine the separate complementary jump and grid errors. -/

theorem Kyprianou.Ch04.ito43_cutoff_combined_error_bound (ja jb jc ga gb gc a Q J : ℝ)
    (hj : |ja-jb-jc| ≤ a*J) (hg : |ga-gb-gc| ≤ a*Q) :
    |(ja-jb-(ga-gb))-(jc-gc)| ≤ a*(Q+J) := by sorry
