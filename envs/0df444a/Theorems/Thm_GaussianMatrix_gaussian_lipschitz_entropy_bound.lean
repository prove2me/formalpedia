-- Prove2me | Theorems.Thm_GaussianMatrix_gaussian_lipschitz_entropy_bound
-- name    : GaussianMatrix.gaussian_lipschitz_entropy_bound
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T04:25:42.612532+00:00
-- url     : https://prove2.me/theorems/990ab0c8-6566-4b16-9dfe-25c3d65d3243
-- title:
--   Gaussian log-Sobolev bound for exponentials of Lipschitz functions: $\mathrm{Ent}_\gamma(e^{sf})\le\frac{s^2L^2}{2}\,\mathbb{E}_\gamma e^{sf}$
-- statement:
--   Let $\iota$ be a finite index set and $\gamma_\iota = \bigotimes_{i\in\iota} N(0,1)$ the standard Gaussian measure on $\mathbb{R}^\iota$. Let $L \in \mathbb{R}$, and let $f : \mathbb{R}^\iota \to \mathbb{R}$ satisfy
--   $$|f(x) - f(y)| \le L\Big(\sum_{i\in\iota}(x_i - y_i)^2\Big)^{1/2} \qquad \text{for all } x, y,$$
--   so that $f$ is $L$-Lipschitz for the Euclidean distance. Then for every $s \in \mathbb{R}$,
--   $$\int s f\, e^{sf}\, d\gamma_\iota - \Big(\int e^{sf}\, d\gamma_\iota\Big)\log\Big(\int e^{sf}\, d\gamma_\iota\Big) \;\le\; \frac{s^2L^2}{2}\int e^{sf}\, d\gamma_\iota ,$$
--   that is, $\mathrm{Ent}_{\gamma_\iota}(e^{sf}) \le \tfrac{s^2L^2}{2}\,\mathbb{E}_{\gamma_\iota} e^{sf}$.
--
--   This is the Gaussian logarithmic Sobolev inequality $\mathrm{Ent}_\gamma(g^2) \le 2\int \|\nabla g\|^2\, d\gamma$ (Gross, 1975) applied to $g = e^{sf/2}$. Here $\|\nabla g\|^2 \le \tfrac{s^2L^2}{4} e^{sf}$ almost everywhere, by Rademacher's theorem, or after approximating $f$ by smooth Lipschitz functions. It is the analytic input of Herbst's argument, which together with the Chernoff bound gives the sharp Gaussian concentration inequality.
--
--   **Formalization Note.** Every integral in the statement is finite, because Lipschitz functions have Gaussian exponential moments of all orders. The hypothesis allows any real $L$. If $L < 0$ and $\iota \neq \emptyset$, the hypothesis cannot hold. If $\iota = \emptyset$, then $f$ is constant and the left-hand side is $0$. The case $s \le 0$ is included and is equally true (replace $f$ by $-f$).
-- source:
--   L. Gross, Logarithmic Sobolev inequalities, Amer. J. Math. 97 (1975); S. Boucheron, G. Lugosi, P. Massart, Concentration Inequalities (Oxford Univ. Press, 2013), Theorem 5.4 (Gaussian logarithmic Sobolev inequality) and the proof of Theorem 5.6, where it is applied to $g = e^{\lambda f/2}$; M. Ledoux, The Concentration of Measure Phenomenon (AMS, 2001), Chapter 5. Numbering is cited from memory.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem gaussian_lipschitz_entropy_bound {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (L : ℝ)
    (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) (s : ℝ) :
    ∫ x, s * f x * Real.exp (s * f x) ∂(Measure.pi fun _ : ι => gaussianReal 0 1)
      - (∫ x, Real.exp (s * f x) ∂(Measure.pi fun _ : ι => gaussianReal 0 1))
        * Real.log (∫ x, Real.exp (s * f x) ∂(Measure.pi fun _ : ι => gaussianReal 0 1))
      ≤ s ^ 2 * L ^ 2 / 2 * ∫ x, Real.exp (s * f x) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  sorry

end GaussianMatrix
