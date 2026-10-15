-- Prove2me | Theorems.Thm_MeasureTheory_lintegral_mul_rieszKernel_ball_le
-- name    : MeasureTheory.lintegral_mul_rieszKernel_ball_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-15T06:59:28.374829+00:00
-- url     : https://prove2.me/theorems/dfade945-a80b-4f23-bbf3-dd142aafc969
-- title:
--   Local first-order potential bound above the dimension
-- statement:
--   Let $n\ge1$ and $n<p<\infty$. There is a finite constant $C_{n,p}\ge0$ such that every Lebesgue almost everywhere strongly measurable function $g:\mathbb R^n\to\mathbb R$, center $x$, and radius $r>0$ satisfy
--
--   $$\int_{B(x,r)}|g(z)|\,|z-x|^{1-n}\,dz\le C_{n,p}\|g\|_{L^p(B(x,r))}\,r^{1-n/p}.$$
--
--   This estimates the local first-order potential for arbitrary measurable data, independently of differentiability or compact support. It is useful in Morrey estimates and local potential bounds.
--
--   **Formalization Note** The integral and norm are extended nonnegative real numbers, allowing infinite norms. The real-power kernel's value at the center is immaterial.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, pp. 69–70, proof of Theorem 3.36, Holder inequality after (3.15) and the radial integral on p. 70; the same estimate is stated for arbitrary measurable scalar data in place of the gradient length.

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory
set_option autoImplicit false

theorem MeasureTheory.lintegral_mul_rieszKernel_ball_le {n : ℕ} {p : ℝ} (hn : 0 < n) (hnp : (n : ℝ) < p) :
    ∃ C : NNReal, ∀ g : EuclideanSpace ℝ (Fin n) → ℝ,
      AEStronglyMeasurable g volume →
      ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      (∫⁻ z in Metric.ball x r, ENNReal.ofReal |g z| *
        ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ)))) ≤
        (C : ENNReal) * eLpNorm g (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x r)) *
            ENNReal.ofReal (r ^ (1 - (n : ℝ) / p)) := by sorry
