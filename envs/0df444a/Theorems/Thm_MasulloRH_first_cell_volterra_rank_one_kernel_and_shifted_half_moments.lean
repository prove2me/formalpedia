-- Prove2me | Theorems.Thm_MasulloRH_first_cell_volterra_rank_one_kernel_and_shifted_half_moments
-- name    : MasulloRH.first_cell_volterra_rank_one_kernel_and_shifted_half_moments
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T19:07:30.03587+00:00
-- url     : https://prove2.me/theorems/7a1e8b8d-0bed-4606-8e1e-12ec4b8c7a69
-- title:
--   First causal cell Volterra rank-one Gram kernel and its signed half-moment convolution trace
-- statement:
--   On the interval [0, log p], adding the reflected causal exponential kernel to its integrated Gram kernel gives exactly exp(x/2) exp(y/2). The shifted column overlap integrated against any continuous real test, divided by p, is its negative-half moment minus its positive-half moment divided by p. The statement includes both integral identities on the actual cell and its full range of coordinates.
-- source:
--   Masullo mission, ordinary first-cell kernel arithmetic for the recentered global Hardy projection. This native theorem isolates the explicit Volterra and overlap calculations; the Hardy projection identification and its zeta factor are separate paper arguments.

import Mathlib
open MeasureTheory

theorem MasulloRH.first_cell_volterra_rank_one_kernel_and_shifted_half_moments (p : ℝ) (hp : 1 < p) (f : ℝ → ℝ) (hf : Continuous f) :
    (∀ x ∈ Set.Icc 0 (Real.log p), ∀ y ∈ Set.Icc 0 (Real.log p),
      Real.exp (|x-y|/2) + (∫ t in (0:ℝ)..min x y,
        Real.exp ((x-t)/2) * Real.exp ((y-t)/2)) =
      Real.exp (x/2) * Real.exp (y/2)) ∧
    (1/p) * (∫ s in (0:ℝ)..Real.log p,
      f s * (∫ x in s..Real.log p, Real.exp ((x-s)/2) * Real.exp (x/2))) =
      (∫ s in (0:ℝ)..Real.log p, f s * Real.exp (-s/2)) -
      (1/p) * (∫ s in (0:ℝ)..Real.log p, f s * Real.exp (s/2)) := by sorry
