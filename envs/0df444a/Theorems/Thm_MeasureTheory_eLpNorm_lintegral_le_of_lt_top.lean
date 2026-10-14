-- Prove2me | Theorems.Thm_MeasureTheory_eLpNorm_lintegral_le_of_lt_top
-- name    : MeasureTheory.eLpNorm_lintegral_le_of_lt_top
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T17:46:22.376423+00:00
-- url     : https://prove2.me/theorems/86a95b04-e229-44a5-b876-7b0c566f0c41
-- title:
--   Nonnegative Minkowski integral inequality with finite mixed norm
-- statement:
--   Let $(\alpha,\mu)$ and $(\beta,\nu)$ be measurable spaces with s-finite measures, let $1<q<\infty$ be a real exponent, and let $G:\alpha\times\beta\to[0,\infty]$ be almost everywhere measurable for the product measure. Suppose
--
--   $$B=\int_\beta\left(\int_\alpha G(x,y)^q\,d\mu(x)\right)^{1/q}d\nu(y)<\infty.$$
--
--   Then
--
--   $$\left(\int_\alpha\left(\int_\beta G(x,y)\,d\nu(y)\right)^q d\mu(x)\right)^{1/q}\le B.$$
--
--   All integrals are nonnegative extended integrals. There is no pointwise finiteness or integrability assumption on the sections. This is the nonnegative mixed-norm form of Minkowski's integral inequality, usable for measurable kernels independently of signed Bochner integration. The endpoint $q=1$ and the infinite-bound case are excluded because they follow directly from Tonelli and the extended order, respectively.
-- source:
--   General nonnegative mixed-norm form of Minkowski integral inequality, derived using Holder and Tonelli or weighted Jensen. John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, Section 1.4, Theorems 1.7 (Jensen) and 1.9 (Holder), printed pp. 4-5, and Appendix 3.C, printed pp. 86-89. This s-finite two-measure interface is a derived generalization, not a verbatim statement in Hunter.

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

open MeasureTheory

theorem MeasureTheory.eLpNorm_lintegral_le_of_lt_top
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {q : ℝ} (hq : 1 < q) (G : α → β → ENNReal)
    (hG : AEMeasurable (Function.uncurry G) (μ.prod ν))
    (hbound : (∫⁻ y, eLpNorm (fun x => G x y) (ENNReal.ofReal q) μ ∂ν) < ⊤) :
    eLpNorm (fun x => ∫⁻ y, G x y ∂ν) (ENNReal.ofReal q) μ ≤
      ∫⁻ y, eLpNorm (fun x => G x y) (ENNReal.ofReal q) μ ∂ν := by sorry
