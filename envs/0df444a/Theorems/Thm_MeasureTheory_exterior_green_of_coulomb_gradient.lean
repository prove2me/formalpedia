-- Prove2me | Theorems.Thm_MeasureTheory_exterior_green_of_coulomb_gradient
-- name    : MeasureTheory.exterior_green_of_coulomb_gradient
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T21:15:35.959719+00:00
-- url     : https://prove2.me/theorems/f6a2d2dd-0eb6-4e48-bf5c-c1ef7604cd52
-- title:
--   Exterior Green formula for a kernel with Coulomb radial gradient
-- statement:
--   Let $n\ge2$, and let $K$ be smooth on $\mathbb R^n\setminus\{0\}$. Suppose that a real constant $c$ satisfies
--
--   $$\partial_iK(z)=c\,|z|^{1-n}\frac{z_i}{|z|}\qquad(z\ne0,\ 1\le i\le n).$$
--
--   Let $f\in C_c^2(\mathbb R^n)$, $x\in\mathbb R^n$, and $r>0$. Suppose $K(z)=\kappa$ whenever $|z|=r$. Write $\alpha_n$ for the volume of the unit ball and $A_f(x,r)$ for the normalized surface average of $f$. Then
--
--   $$\int_{\mathbb R^n\setminus B_r(x)}K(x-y)\Delta f(y)\,dy=-\kappa\int_{B_r(x)}\Delta f(y)\,dy+n\alpha_n c\,A_f(x,r).$$
--
--   This is the compact-support exterior specialization of Green's second identity, with the derivative flux expressed as a ball Laplacian integral. It applies to arbitrary scalar multiples and additive constants of the logarithmic and Newtonian kernels, and isolates the integration-by-parts step from singular-radius limits.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, printed p. 32, Eq. (2.11); pp. 33–36, Eqs. (2.14), (2.15), (2.20); p. 17, Theorem 1.46. Generalization allowing an arbitrary gradient coefficient and boundary constant.

import Definitions.Def_HunterPDE_Harmonic_MeanValue
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.ContDiff.Basic

open MeasureTheory Set
open scoped ContDiff
open Laplacian
open HunterPDE.Harmonic

theorem MeasureTheory.exterior_green_of_coulomb_gradient
    (n : ℕ) (hn : 2 ≤ n) (K : EuclideanSpace ℝ (Fin n) → ℝ)
    (hK : ContDiffOn ℝ ∞ K {0}ᶜ) (c : ℝ)
    (hDK : ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 → ∀ i : Fin n,
      fderiv ℝ K z (EuclideanSpace.single i 1) =
        c * (1 / ‖z‖ ^ (n - 1)) * (z i / ‖z‖))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (x : EuclideanSpace ℝ (Fin n))
    (r : ℝ) (hr : 0 < r) (κ : ℝ)
    (hκ : ∀ z : EuclideanSpace ℝ (Fin n), ‖z‖ = r → K z = κ) :
    (∫ y in (Metric.ball x r)ᶜ, K (x - y) * (Δ f) y) =
      -κ * (∫ y in Metric.ball x r, (Δ f) y) +
        ((n : ℝ) * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) * c) *
          sphereAverage f x r := by sorry
