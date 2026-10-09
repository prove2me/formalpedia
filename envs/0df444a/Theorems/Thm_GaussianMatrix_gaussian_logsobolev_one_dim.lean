-- Prove2me | Theorems.Thm_GaussianMatrix_gaussian_logsobolev_one_dim
-- name    : GaussianMatrix.gaussian_logsobolev_one_dim
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T06:53:09.494919+00:00
-- url     : https://prove2.me/theorems/a327531a-4492-4992-b6a7-d3b9886139aa
-- title:
--   One-dimensional Gaussian logarithmic Sobolev inequality: $\mathrm{Ent}_\gamma(g^2)\le 2\int (g')^2\,d\gamma$ for $C^1$ functions $g:\mathbb{R}\to\mathbb{R}$
-- statement:
--   Let $\gamma = N(0,1)$ be the standard Gaussian measure on $\mathbb{R}$. Let $g : \mathbb{R} \to \mathbb{R}$ be continuously differentiable, and assume that $g^2$, $g^2 \log g^2$ and $(g')^2$ are $\gamma$-integrable (with the convention $0 \log 0 = 0$). Then
--   $$\int g^2 \log g^2 \, d\gamma \;-\; \Big(\int g^2\, d\gamma\Big) \log\Big(\int g^2 \, d\gamma\Big) \;\le\; 2 \int (g')^2 \, d\gamma .$$
--   The left-hand side is the entropy $\mathrm{Ent}_\gamma(g^2)$ of the nonnegative function $g^2$.
--
--   This is Gross's logarithmic Sobolev inequality for the Gaussian measure in dimension one, with the sharp constant $2$. Together with the tensorization of entropy it yields the inequality on $\mathbb{R}^\iota$ (`gaussian_logsobolev`), which in turn gives the entropy bound $\mathrm{Ent}(e^{sf}) \le \tfrac{s^2L^2}{2}\mathbb{E}e^{sf}$ for Lipschitz $f$ used in Herbst's argument. It is the only analytic input of the whole chain that is not elementary.
--
--   **Formalization Note.** The derivative is `deriv g`, and $C^1$ is `ContDiff ℝ 1 g`. The integrability hypotheses guarantee that all Bochner integrals in the statement are the true (finite) integrals; `Real.log 0 = 0` matches the convention $0\log 0 = 0$. The hypotheses on $g^2$ and $g^2\log g^2$ are in fact consequences of the others (Gaussian Poincaré inequality and the inequality itself) but are included to keep the statement transparent. Constant $g$ gives $0 \le 0$.
-- source:
--   L. Gross, Logarithmic Sobolev inequalities, Amer. J. Math. 97 (1975), 1061–1083 (Gaussian case, proved via the two-point inequality and the central limit theorem); S. Boucheron, G. Lugosi, P. Massart, Concentration Inequalities (Oxford Univ. Press, 2013), Theorem 5.4 (Gaussian logarithmic Sobolev inequality), case $n = 1$; M. Ledoux, The Concentration of Measure Phenomenon (AMS, 2001), §5.1, inequality (5.1) / Theorem 5.1. Theorem and equation numbers are cited from memory and should be checked.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem gaussian_logsobolev_one_dim (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun t => g t ^ 2) (gaussianReal 0 1))
    (hglog : Integrable (fun t => g t ^ 2 * Real.log (g t ^ 2)) (gaussianReal 0 1))
    (hdg : Integrable (fun t => deriv g t ^ 2) (gaussianReal 0 1)) :
    ∫ t, g t ^ 2 * Real.log (g t ^ 2) ∂(gaussianReal 0 1)
      - (∫ t, g t ^ 2 ∂(gaussianReal 0 1)) * Real.log (∫ t, g t ^ 2 ∂(gaussianReal 0 1))
      ≤ 2 * ∫ t, deriv g t ^ 2 ∂(gaussianReal 0 1) := by
  sorry

end GaussianMatrix
