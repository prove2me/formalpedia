-- Prove2me | Theorems.Thm_MasulloRH_truncated_euler_circle_second_derivative_gram
-- name    : MasulloRH.truncated_euler_circle_second_derivative_gram
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T12:22:27.456182+00:00
-- url     : https://prove2.me/theorems/00d9f66b-97b3-4efc-bfb0-a3326c10c9a9
-- title:
--   Exact fifth-degree Gram growth of the second derivative of a truncated prime-circle Euler inverse
-- statement:
--   On the real additive circle of period T>0, the Fourier packet of the first N consecutive Euler translates has second derivative equal to the quadratically weighted packet times minus (2 pi/T)^2. The squared normalized Haar L2 norm of the quadratically weighted packet is N(N-1)(2N-1)(3N^2-3N-1)/30. Thus its L2 norm has exact order N^(5/2), for instance on a prime Mellin lattice T=2 pi/log p.
-- source:
--   Critical weighted global Euler inverse cutoff in the Masullo mission. Uses Mathlib normalized Haar Fourier orthogonality.

import Mathlib
open AddCircle MeasureTheory
open scoped Real

theorem MasulloRH.truncated_euler_circle_second_derivative_gram (T : ℝ) [Fact (0 < T)] (N : ℕ) :
    let P := fun x : ℝ => ∑ j ∈ Finset.range N, fourier (j:ℤ) (x : AddCircle T)
    (∀ x : ℝ, deriv (deriv P) x =
      -((2 * Real.pi / T : ℝ) : ℂ)^2 *
        ∑ j ∈ Finset.range N, (j:ℂ)^2 * fourier (j:ℤ) (x : AddCircle T)) ∧
    ‖∑ j ∈ Finset.range N, (j:ℂ)^2 • (@fourierLp T _ 2 _ (j:ℤ))‖^2 =
      (N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)*(3*(N:ℝ)^2-3*(N:ℝ)-1)/30 := by sorry
