-- Prove2me | Theorems.Thm_MeasureTheory_eLpNorm_integral_le_lintegral
-- name    : MeasureTheory.eLpNorm_integral_le_lintegral
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T14:37:52.584295+00:00
-- url     : https://prove2.me/theorems/d0310cdf-e1f8-4290-9f6d-306a7175260d
-- title:
--   Minkowski integral inequality for finite Lp seminorms
-- statement:
--   Let $(\alpha,\mu)$ and $(\beta,\nu)$ be measurable spaces with sigma-finite or, more generally, s-finite measures, and let $1\le p<\infty$. Let $F:\alpha\times\beta\to\mathbb R$ be almost everywhere strongly measurable for the product measure. Suppose $F(x,\cdot)$ is integrable with respect to $\nu$ for almost every $x$. Then
--
--   $$\left\|x\mapsto\int_\beta F(x,y)\,d\nu(y)\right\|_{L^p(\mu)}
--   \le \int_\beta\|F(\cdot,y)\|_{L^p(\mu)}\,d\nu(y).$$
--
--   The right side is an extended nonnegative integral, so no finite upper-bound hypothesis is imposed. The statement concerns scalar real functions and includes $p=1$. It separates the integral norm estimate from any convolution or translation structure.
-- source:
--   Minkowski integral inequality, the integral form of the Lp triangle inequality. Derived from Holder and Tonelli (or normalized Jensen): John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, Section 1.4, Theorem 1.7 (printed p. 4), and Appendix 3.C on integration (printed pp. 86-89). The two-measure s-finite formulation is a general measure-theoretic interface, not a verbatim theorem in Hunter.

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

open MeasureTheory

theorem MeasureTheory.eLpNorm_integral_le_lintegral
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {p : ENNReal} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (F : α → β → ℝ)
    (hF : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν))
    (hFi : ∀ᵐ x ∂μ, Integrable (F x) ν) :
    eLpNorm (fun x => ∫ y, F x y ∂ν) p μ ≤
      ∫⁻ y, eLpNorm (fun x => F x y) p μ ∂ν := by sorry
