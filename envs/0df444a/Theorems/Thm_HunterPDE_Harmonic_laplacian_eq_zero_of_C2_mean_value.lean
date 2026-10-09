-- Prove2me | Theorems.Thm_HunterPDE_Harmonic_laplacian_eq_zero_of_C2_mean_value
-- name    : HunterPDE.Harmonic.laplacian_eq_zero_of_C2_mean_value
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T11:14:37.121247+00:00
-- url     : https://prove2.me/theorems/ff95cd2c-0864-4499-9a34-2ef824b962ba
-- title:
--   The mean-value property forces the Laplacian of a C2 function to vanish
-- statement:
--   Let $n\ge1$, let $\Omega\subseteq\mathbb R^n$ be open, and let $u$ be $C^2$ on $\Omega$ with Hunter's ball and sphere mean-value property. Then
--
--   $$\Delta u(x)=0\qquad(x\in\Omega).$$
--
--   This isolates the differential consequence of the mean-value property from the mollification argument establishing smoothness.
-- source:
--   Hunter, Notes on PDEs (revised 6/18/2014), printed p. 21, proof of Theorem 2.2; https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf. Kernel construction: Mathlib Analysis/Calculus/BumpFunction/InnerProduct.lean.

import Theorems.Thm_HunterPDE_Harmonic_sphereAverage_radial_eq_ball_laplacian
import Theorems.Thm_HunterPDE_Harmonic_hasDerivAt_sphereAverage_radial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open MeasureTheory Set Metric Filter Laplacian HunterPDE.Harmonic
open scoped Topology
set_option autoImplicit false

theorem HunterPDE.Harmonic.laplacian_eq_zero_of_C2_mean_value {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 2 u Ω) (hmv : HasMeanValueProperty Ω u) :
    ∀ x ∈ Ω, Δ u x = 0 := by sorry
