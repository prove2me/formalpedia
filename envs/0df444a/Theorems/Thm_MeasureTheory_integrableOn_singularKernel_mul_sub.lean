-- Prove2me | Theorems.Thm_MeasureTheory_integrableOn_singularKernel_mul_sub
-- name    : MeasureTheory.integrableOn_singularKernel_mul_sub
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T10:10:17.088543+00:00
-- url     : https://prove2.me/theorems/9d079909-c4a1-47e9-bfd0-b1aca273e597
-- title:
--   C1 cancellation makes a critical singular kernel integrable on finite balls
-- statement:
--   Let $n\ge1$, let $f:\mathbb R^n\to\mathbb R$ be continuously differentiable, and let $K:\mathbb R^n\to\mathbb R$ be almost everywhere strongly measurable for Lebesgue measure. Suppose $C\ge0$ and $|K(z)|\le C|z|^{-n}$ for every $z\ne0$. For every $R>0$, the cancelled product is absolutely integrable:
--
--   $$K(\cdot)(f(\cdot)-f(0))\in L^1(B_R(0)).$$
--
--   This general form of first-order cancellation applies to critical singular kernels, including entries of the Newtonian Hessian. No support assumption on the source is needed.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf, printed p. 38, Theorem 2.26 Eq. (2.27), general measurable-kernel version of its first-order cancellation integrability argument.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MeasureTheory
open scoped ContDiff
set_option autoImplicit false

theorem MeasureTheory.integrableOn_singularKernel_mul_sub (n : ℕ) (hn : 1 ≤ n)
    (K f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hK : AEStronglyMeasurable K volume) (hf : ContDiff ℝ 1 f)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z, z ≠ 0 → ‖K z‖ ≤ C * ‖z‖ ^ (-(n : ℝ)))
    (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun z => K z * (f z - f 0)) (Metric.ball 0 R) := by sorry
