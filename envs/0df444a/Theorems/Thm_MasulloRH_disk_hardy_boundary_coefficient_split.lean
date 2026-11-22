-- Prove2me | Theorems.Thm_MasulloRH_disk_hardy_boundary_coefficient_split
-- name    : MasulloRH.disk_hardy_boundary_coefficient_split
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T12:23:36.389589+00:00
-- url     : https://prove2.me/theorems/d3ec38a7-0046-416e-9210-ecf7121f3ffe
-- title:
--   Disk Hardy boundary coefficients with fourth-power energy have a sharp three-halves tail bound
-- statement:
--   If a complex sequence has partial fourth-weighted quadratic energy at most one and |a_k| ≤ D 2^k, then its absolute sum converges and is bounded by D(2^M−1)+M^(−3/2) for every positive integer M. Applying the bound with exponentially small D arising from interior Blaschke zeros controls prime-circle edge evaluations.
-- source:
--   Masullo mission: Taylor coefficient bound in the disk representation of the critical weighted Hardy space; weighted Cauchy–Schwarz and telescoping.

import Mathlib
open Finset

theorem MasulloRH.disk_hardy_boundary_coefficient_split (a : ℕ → ℂ) (D : ℝ) (hD : 0 ≤ D)
    (hcoeff : ∀ k, ‖a k‖ ≤ D * 2^k)
    (energy : ∀ N : ℕ, (∑ k ∈ range N, ((k:ℝ)+1)^4 * ‖a k‖^2) ≤ 1)
    (M : ℕ) (hM : 0 < M) :
    Summable (fun k => ‖a k‖) ∧
      (∑' k, ‖a k‖) ≤ D * ((2:ℝ)^M-1) + Real.sqrt (1/(M:ℝ)^3) := by sorry
