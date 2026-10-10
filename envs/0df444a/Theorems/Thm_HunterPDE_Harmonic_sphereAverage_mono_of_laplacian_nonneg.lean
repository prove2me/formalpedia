-- Prove2me | Theorems.Thm_HunterPDE_Harmonic_sphereAverage_mono_of_laplacian_nonneg
-- name    : HunterPDE.Harmonic.sphereAverage_mono_of_laplacian_nonneg
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T14:24:14.132+00:00
-- url     : https://prove2.me/theorems/f9da7329-952a-4d04-8886-778469e7db99
-- title:
--   Spherical averages increase when the Laplacian is nonnegative
-- statement:
--   Let n ≥ 1 and r > 0. Suppose u is twice continuously differentiable near every point of the closed ball of radius r centered at x, and its Laplacian is nonnegative on the open ball. Then the normalized spherical mean of u about x is nondecreasing as its radius varies over [0,r]. Continuity includes radius zero, where the mean equals u(x). This is the differential step of Hunter’s Theorem 2.5, using equation (2.4).
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, p. 22, Theorem 2.5; p. 20, equation (2.4) and polar integration in the proof of Theorem 2.1. https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf

import Theorems.Thm_HunterPDE_Harmonic_sphereAverage_continuousOn
import Theorems.Thm_HunterPDE_Harmonic_hasDerivAt_sphereAverage_radial
import Theorems.Thm_HunterPDE_Harmonic_sphereAverage_radial_eq_ball_laplacian
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open MeasureTheory Set HunterPDE.Harmonic
set_option autoImplicit false

theorem HunterPDE.Harmonic.sphereAverage_mono_of_laplacian_nonneg {n : ℕ} (hn : 0 < n) {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hu : ∀ y ∈ Metric.closedBall x r, ContDiffAt ℝ 2 u y)
    (hΔ : ∀ y ∈ Metric.ball x r, 0 ≤ Laplacian.laplacian u y) :
    MonotoneOn (sphereAverage u x) (Icc 0 r) := by sorry
