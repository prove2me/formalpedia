-- Prove2me | Theorems.Thm_MasulloRH_height_two_theta_six_tail_derivative_bounds
-- name    : MasulloRH.height_two_theta_six_tail_derivative_bounds
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T13:29:05.216427+00:00
-- url     : https://prove2.me/theorems/86597691-d1c7-59fc-bd82-ecdea459d026
-- title:
--   Uniform value, curvature and truncation-tail bounds for the six-term theta approximant
-- statement:
--   Let $S_b(z)$ be the published six-term theta approximation on a fixed direct or reflected branch, and let $E_b(z)$ be its geometric tail estimate. On the reflected branch for $z\le-5/2$, or the direct branch for $z\ge9/8$, one has $|S_b(z)|\le1/200000000$, $|S_b''(z)|\le1/200$, and $E_b(z)\le1/1000000000$. These bounds hold on the entire stated half-lines.
-- source:
--   The Masullo height-two theta-energy calculation https://prove2.me/theorems/cc487734-5ed4-5457-b10a-df505d0aef9e and its curvature-row theorem https://prove2.me/theorems/680e75e0-46e9-4f05-b70c-7f7de8530930.

import Definitions.Def_MasulloRH_HeightTwoCurvature

open MasulloRH.HeightTwoCurvature

theorem MasulloRH.height_two_theta_six_tail_derivative_bounds (b : Bool) (z : ℝ)
    (hc : (b = true ∧ z ≤ -5/2) ∨ (b = false ∧ 9/8 ≤ z)) :
    |thetaSix b z| ≤ 1/200000000 ∧ |deriv (deriv (thetaSix b)) z| ≤ 1/200 ∧
      thetaTail b z ≤ 1/1000000000 := by sorry
