-- Prove2me | Theorems.Thm_MeasureTheory_laplacian_convolution_right
-- name    : MeasureTheory.laplacian_convolution_right
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T22:37:38.347788+00:00
-- url     : https://prove2.me/theorems/e9bddba8-372e-4e78-bd5f-71fd960a16fc
-- title:
--   Laplacian commutes with convolution against a locally integrable kernel
-- statement:
--   Let K be a locally Lebesgue integrable real function on Euclidean n-space, and let f be a twice continuously differentiable real function with compact support. Then the Laplacian of K convolved with f equals K convolved with the Laplacian of f. No global integrability or differentiability of K is required. This differentiation-on-the-smooth-factor identity applies to singular kernels and in particular Newtonian potentials.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), Theorem 2.25, printed p. 34, differentiation under the convolution integral; https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf. Generalized to arbitrary locally integrable kernels and C2 compactly supported sources using Mathlib HasCompactSupport.hasFDerivAt_convolution_right.

import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory ContinuousLinearMap
open scoped Convolution ContDiff
open Laplacian

theorem MeasureTheory.laplacian_convolution_right (n : ℕ) (K f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hK : LocallyIntegrable K volume) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    Δ (K ⋆[lsmul ℝ ℝ] f) = K ⋆[lsmul ℝ ℝ] (Δ f) := by sorry
