-- Prove2me | Theorems.Thm_HunterPDE_Newtonian_cancelled_hessian_near_bound
-- name    : HunterPDE.Newtonian.cancelled_hessian_near_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T17:08:15.365133+00:00
-- url     : https://prove2.me/theorems/9b6c550c-9a74-4e0b-8614-d66a0b558fbd
-- title:
--   Uniform near-singularity bound for cancelled Newtonian Hessian integrals
-- statement:
--   Let $n\ge2$ and $\alpha>0$. There exists $A\ge0$, depending only on $n$ and $\alpha$, such that for every continuous $f:\mathbb R^n\to\mathbb R$ and $H\ge0$ satisfying $|f(x)-f(y)|\le H\|x-y\|^\alpha$ for all points, every $x$, $R>0$ and coordinate indices $i,j$, the cancelled Newtonian Hessian integrand is integrable on $B_R(x)$ and
--
--   $$\left|\int_{B_R(x)}\partial_{ij}\Gamma(x-y)[f(y)-f(x)]\,dy\right|\le AH R^\alpha.$$
--
--   The same constant applies to all coordinate pairs. Smoothness and compact support of the source are not needed for this local estimate; it is the individual near-singularity bound used in the Holder proof.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf, printed p. 41, Theorem 2.28 proof, part (a). Uniform-coordinate formulation of the individual centred near-singularity estimate, with weaker source regularity hypotheses.

import Theorems.Thm_MeasureTheory_singularKernel_holder_near_bound
import Theorems.Thm_HunterPDE_Newtonian_fundamentalSolution_partial
import Theorems.Thm_HunterPDE_Newtonian_norm_secondPartial_le
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory HunterPDE.Newtonian
open scoped ContDiff NNReal
set_option autoImplicit false

theorem HunterPDE.Newtonian.cancelled_hessian_near_bound (n : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα : 0 < α) :
    ∃ A : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, Continuous f →
      ∀ H : ℝ≥0, (∀ x y, |f x - f y| ≤ (H : ℝ) * ‖x - y‖ ^ α) →
      ∀ x : EuclideanSpace ℝ (Fin n), ∀ R : ℝ, 0 < R → ∀ i j : Fin n,
        IntegrableOn (fun y => secondPartial (fundamentalSolution n) i j (x - y) *
            (f y - f x)) (Metric.ball x R) ∧
          |∫ y in Metric.ball x R, secondPartial (fundamentalSolution n) i j (x - y) *
              (f y - f x)| ≤ (A : ℝ) * (H : ℝ) * R ^ α := by sorry
