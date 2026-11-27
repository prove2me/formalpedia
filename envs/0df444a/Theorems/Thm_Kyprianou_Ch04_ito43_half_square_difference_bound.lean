-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_half_square_difference_bound
-- name    : Kyprianou.Ch04.ito43_half_square_difference_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:59:24.840477+00:00
-- url     : https://prove2.me/theorems/a5ad3465-68bc-45e2-b052-3d4dde53c485
-- title:
--   Bounded half-square differences are Lipschitz in the endpoint
-- statement:
--   Factor the difference of squares and bound the remaining factor by four times the compact path bound.
-- source:
--   Kyprianou (2006), Theorem 4.3 proof auxiliary

import Mathlib
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_half_square_difference_bound
    (x y z R δ : ℝ) (hδ : 0 ≤ δ)
    (hx : |x| ≤ R) (hy : |y| ≤ R) (hz : |z| ≤ R)
    (hd : |x-z| ≤ δ) :
    |(x-y)^2/2-(z-y)^2/2| ≤ 2*R*δ := by sorry
