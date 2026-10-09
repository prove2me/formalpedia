-- Prove2me | Theorems.Thm_MeasureTheory_exists_smooth_radial_probability_kernel
-- name    : MeasureTheory.exists_smooth_radial_probability_kernel
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T11:10:16.587054+00:00
-- url     : https://prove2.me/theorems/179af916-cd7d-46b2-b5ad-2601ec7c569d
-- title:
--   Smooth radial kernels of unit integral
-- statement:
--   For every radius $R>0$ and every $n\ge0$, there is a smooth compactly supported radial function $k$ on $\mathbb R^n$, with profile $\kappa$, such that
--
--   $$k(y)=\kappa(\lVert y\rVert),\qquad k(y)=0\text{ if }\lVert y\rVert\ge R,\qquad \int k=1.$$
--
--   The kernel can be chosen nonnegative; that extra property is not part of this interface.
-- source:
--   Hunter, Notes on PDEs (revised 6/18/2014), printed p. 21, proof of Theorem 2.2; https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf. Kernel construction: Mathlib Analysis/Calculus/BumpFunction/InnerProduct.lean.

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Set Metric Function
open scoped ContDiff Topology
set_option autoImplicit false

theorem MeasureTheory.exists_smooth_radial_probability_kernel {n : ℕ} {R : ℝ} (hR : 0 < R) :
    ∃ (k : EuclideanSpace ℝ (Fin n) → ℝ) (κ : ℝ → ℝ),
      ContDiff ℝ ∞ k ∧ HasCompactSupport k ∧
      (∀ y, k y = κ ‖y‖) ∧ (∀ y, R ≤ ‖y‖ → k y = 0) ∧
      (∫ y, k y) = 1 := by sorry
