-- Prove2me | Theorems.Thm_MeasureTheory_radial_convolution_eq_of_sphere_average
-- name    : MeasureTheory.radial_convolution_eq_of_sphere_average
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T11:10:40.39982+00:00
-- url     : https://prove2.me/theorems/0ceaed90-ab03-4590-bead-55c601206ca5
-- title:
--   Radial convolution reproduces a constant spherical mean
-- statement:
--   Let $n\ge1$. Suppose $k:\mathbb R^n\to\mathbb R$ is continuous, compactly supported, radial with profile $\kappa$, vanishes when $\lVert y\rVert\ge R$, and has integral one. Let $g$ be locally integrable. If every spherical average of $g$ centered at $x$ with radius $0<r<R$ equals $g(x)$, then
--
--   $$(k*g)(x)=g(x).$$
--
--   No global continuity of $g$ is required.
-- source:
--   Hunter, Notes on PDEs (revised 6/18/2014), printed p. 21, proof of Theorem 2.2; https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf. Kernel construction: Mathlib Analysis/Calculus/BumpFunction/InnerProduct.lean.

import Theorems.Thm_MeasureTheory_integral_polar_sphere_centered
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open MeasureTheory Set Metric Filter
open scoped Topology Convolution
set_option autoImplicit false

theorem MeasureTheory.radial_convolution_eq_of_sphere_average {n : ℕ} (hn : 0 < n)
    {k g : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ → ℝ} {R : ℝ}
    (hk : Continuous k) (hkc : HasCompactSupport k)
    (hkr : ∀ y, k y = κ ‖y‖) (hks : ∀ y, R ≤ ‖y‖ → k y = 0)
    (hki : ∫ y, k y = 1) (hg : LocallyIntegrable g)
    (x : EuclideanSpace ℝ (Fin n))
    (hmean : ∀ r : ℝ, 0 < r → r < R →
      (⨍ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        g (x + r • ω.1) ∂volume.toSphere) = g x) :
    (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x = g x := by sorry
