-- Prove2me | Theorems.Thm_GaussianMatrix_entropy_tensorization
-- name    : GaussianMatrix.entropy_tensorization
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T07:49:22.85998+00:00
-- url     : https://prove2.me/theorems/e0cde296-d9d2-4c20-9412-571c50a44b23
-- title:
--   Tensorization (subadditivity) of entropy for product probability measures: $\mathrm{Ent}_{\otimes\mu_i}(h)\le\sum_i\int\mathrm{Ent}_{\mu_i}(h)\,d\mu$
-- statement:
--   Let $\iota$ be a finite index set, $(\Omega, \mathcal{F})$ a measurable space, and $\mu_i$ ($i\in\iota$) probability measures on $\Omega$. Let $\mu = \bigotimes_{i\in\iota}\mu_i$ be the product measure on $\Omega^\iota$. For $x \in \Omega^\iota$, $i \in \iota$ and $t \in \Omega$ write $x^{(i\leftarrow t)}$ for the point obtained from $x$ by replacing its $i$-th coordinate with $t$. For a positive function $\varphi$ on a probability space $(E,\nu)$ let $\mathrm{Ent}_\nu(\varphi) = \int \varphi\log\varphi\,d\nu - \big(\int\varphi\,d\nu\big)\log\big(\int\varphi\,d\nu\big)$.
--
--   Let $h : \Omega^\iota \to (0,\infty)$ be measurable, with $h$ and $h \log h$ both $\mu$-integrable. Then
--   $$\mathrm{Ent}_\mu(h) \;\le\; \sum_{i\in\iota} \int_{\Omega^\iota} \mathrm{Ent}_{\mu_i}\big(t \mapsto h(x^{(i\leftarrow t)})\big)\, d\mu(x),$$
--   that is,
--   $$\int h\log h\,d\mu - \Big(\int h\,d\mu\Big)\log\Big(\int h\,d\mu\Big) \le \sum_{i} \int \Big[\int h(x^{(i\leftarrow t)}) \log h(x^{(i\leftarrow t)})\,d\mu_i(t) - \Big(\int h(x^{(i\leftarrow t)})\,d\mu_i(t)\Big)\log\Big(\int h(x^{(i\leftarrow t)})\,d\mu_i(t)\Big)\Big]\,d\mu(x).$$
--
--   The inner bracket depends only on the coordinates of $x$ other than $i$, so this is the usual statement that the entropy of a product measure is bounded by the sum of the expected conditional (one-coordinate) entropies. It reduces log-Sobolev inequalities on product spaces to one-dimensional ones; for the Gaussian measure it turns the one-dimensional log-Sobolev inequality into the dimension-free inequality on $\mathbb{R}^\iota$.
--
--   **Formalization Note.** The product measure is `Measure.pi μ` on `ι → Ω` and $x^{(i\leftarrow t)}$ is `Function.update x i t` (hence `[DecidableEq ι]`). The function is assumed strictly positive, which is all that the application ($h = g^2+\delta$) needs; the general nonnegative case follows by approximation but is not claimed here. For $\mu$-almost every $x$ the sections are integrable, and the outer integrands are genuinely integrable, so the Bochner conventions play no role. For $\iota = \emptyset$ both sides are $0$.
-- source:
--   M. Ledoux, The Concentration of Measure Phenomenon (AMS, 2001), Proposition 5.6 (tensorization of entropy); S. Boucheron, G. Lugosi, P. Massart, Concentration Inequalities (Oxford Univ. Press, 2013), Chapter 4, sub-additivity of entropy (Theorem 4.10 there, proved via the duality formula Theorem 4.13; numbering uncertain); M. Ledoux, Concentration of measure and logarithmic Sobolev inequalities, Séminaire de Probabilités XXXIII, LNM 1709 (1999), §5. All numbering is cited from memory.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem entropy_tensorization {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*}
    [MeasurableSpace Ω] (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (h : (ι → Ω) → ℝ) (hmeas : Measurable h) (hpos : ∀ x, 0 < h x)
    (hint : Integrable h (Measure.pi μ))
    (hlog : Integrable (fun x => h x * Real.log (h x)) (Measure.pi μ)) :
    ∫ x, h x * Real.log (h x) ∂(Measure.pi μ)
      - (∫ x, h x ∂(Measure.pi μ)) * Real.log (∫ x, h x ∂(Measure.pi μ))
      ≤ ∑ i, ∫ x, (∫ t, h (Function.update x i t) * Real.log (h (Function.update x i t)) ∂(μ i)
          - (∫ t, h (Function.update x i t) ∂(μ i))
            * Real.log (∫ t, h (Function.update x i t) ∂(μ i))) ∂(Measure.pi μ) := by
  sorry

end GaussianMatrix
