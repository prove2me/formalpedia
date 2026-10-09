-- Prove2me | Theorems.Thm_GaussianMatrix_gaussian_logsobolev
-- name    : GaussianMatrix.gaussian_logsobolev
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T07:49:55.263593+00:00
-- url     : https://prove2.me/theorems/e4a25958-6209-420f-a407-6bf7c0ba59cd
-- title:
--   Gaussian logarithmic Sobolev inequality on $\mathbb{R}^\iota$: $\mathrm{Ent}_{\gamma_\iota}(g^2)\le 2\int\|\nabla g\|_2^2\,d\gamma_\iota$ for $C^1$ functions $g$
-- statement:
--   Let $\iota$ be a finite index set and $\gamma_\iota = \bigotimes_{i\in\iota} N(0,1)$ the standard Gaussian measure on $\mathbb{R}^\iota$. Let $g : \mathbb{R}^\iota \to \mathbb{R}$ be continuously differentiable, with partial derivatives $\partial_i g(x) = Dg(x)\,e_i$, and assume that $g^2$, $g^2\log g^2$ and $\|\nabla g\|_2^2 = \sum_{i\in\iota}(\partial_i g)^2$ are $\gamma_\iota$-integrable. Then
--   $$\int g^2\log g^2\,d\gamma_\iota - \Big(\int g^2\,d\gamma_\iota\Big)\log\Big(\int g^2\,d\gamma_\iota\Big) \;\le\; 2\int \sum_{i\in\iota} (\partial_i g)^2\, d\gamma_\iota .$$
--
--   This is Gross's dimension-free logarithmic Sobolev inequality for the standard Gaussian measure. Applied to $g = e^{sf/2}$ with $\|\nabla f\|_2 \le L$ it gives $\mathrm{Ent}(e^{sf}) \le \tfrac{s^2L^2}{2}\,\mathbb{E}e^{sf}$, the input of Herbst's argument for sharp Gaussian concentration.
--
--   **Formalization Note.** The partial derivative is `fderiv ℝ g x (Pi.single i 1)`; the Euclidean norm of the gradient is written out as a sum of squares (the default norm on `ι → ℝ` is the sup norm, but `fderiv` does not depend on the choice of norm). $C^1$ is `ContDiff ℝ 1 g`. With the integrability hypotheses every Bochner integral in the statement is a true integral. For $\iota = \emptyset$, $g$ is constant and both sides are $0$.
-- source:
--   L. Gross, Logarithmic Sobolev inequalities, Amer. J. Math. 97 (1975), 1061–1083; S. Boucheron, G. Lugosi, P. Massart, Concentration Inequalities (Oxford Univ. Press, 2013), Theorem 5.4 (Gaussian logarithmic Sobolev inequality); M. Ledoux, The Concentration of Measure Phenomenon (AMS, 2001), §5.1 / (5.1). Numbering is cited from memory.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem gaussian_logsobolev {ι : Type*} [Fintype ι] [DecidableEq ι] (g : (ι → ℝ) → ℝ)
    (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2) (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hglog : Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2))
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hdg : Integrable (fun x => ∑ i, fderiv ℝ g x (Pi.single i 1) ^ 2)
      (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    ∫ x, g x ^ 2 * Real.log (g x ^ 2) ∂(Measure.pi fun _ : ι => gaussianReal 0 1)
      - (∫ x, g x ^ 2 ∂(Measure.pi fun _ : ι => gaussianReal 0 1))
        * Real.log (∫ x, g x ^ 2 ∂(Measure.pi fun _ : ι => gaussianReal 0 1))
      ≤ 2 * ∫ x, ∑ i, fderiv ℝ g x (Pi.single i 1) ^ 2
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  sorry

end GaussianMatrix
