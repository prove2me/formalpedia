-- Prove2me | Theorems.Thm_MasulloRH_critical_width_square_root_cutoff_borderline_schedule
-- name    : MasulloRH.critical_width_square_root_cutoff_borderline_schedule
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T07:08:06.274171+00:00
-- url     : https://prove2.me/theorems/07404d08-b564-412c-8d78-27851e29fe7d
-- title:
--   An explicit critical-width cutoff reaches the square-root norm borderline
-- statement:
--   Let L=n exp(n), d=2n, X=exp(L), and Λ=exp(L−d). Then Λ is asymptotic to X(loglog X/log X)² as real n→∞, and the normalized critical-width operator-weight factor exp(−d)(1+L²)/(1+d²) converges to 1/4. The schedule tests the boundary of a sufficient weighted norm estimate and determines no trace coefficient.
-- source:
--   Masullo, Sections 9.2 and 11.3–12.4; cutoff benchmark for the critical-width global weight.

import Mathlib
open Filter Topology

theorem MasulloRH.critical_width_square_root_cutoff_borderline_schedule :
    let L : ℝ → ℝ := fun n => n * Real.exp n
    let d : ℝ → ℝ := fun n => 2*n
    let X : ℝ → ℝ := fun n => Real.exp (L n)
    let cutoff : ℝ → ℝ := fun n => Real.exp (L n - d n)
    Tendsto (fun n => X n * (Real.log (Real.log (X n)) / Real.log (X n))^2 / cutoff n)
      atTop (𝓝 1) ∧
    Tendsto (fun n => Real.exp (-(d n)) * (1+(L n)^2)/(1+(d n)^2))
      atTop (𝓝 (1/4 : ℝ)) := by sorry
