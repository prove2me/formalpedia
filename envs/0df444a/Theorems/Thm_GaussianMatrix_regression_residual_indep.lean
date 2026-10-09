-- Prove2me | Theorems.Thm_GaussianMatrix_regression_residual_indep
-- name    : GaussianMatrix.regression_residual_indep
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T06:18:12.128881+00:00
-- url     : https://prove2.me/theorems/a07c80ff-5cd2-4fce-abd4-35b9a20c4bdc
-- title:
--   For $g\sim\mathcal{N}(0,I_k)$ and fixed full-row-rank $H$, $Hg$ is independent of the squared residual $\|(I-P_H)g\|^2$
-- statement:
--   Let $H \in \mathbb{R}^{n\times k}$ be a fixed matrix with $\operatorname{rank} H = n$, so that $HH^\top$ is invertible, and let $g \sim \mathcal{N}(0, I_k)$ have independent standard normal coordinates. Define the squared residual
--
--   $$Q_H(g) \;=\; g^\top g - (Hg)^\top (HH^\top)^{-1}(Hg) \;=\; \|(I-P_H)\,g\|_2^2, \qquad P_H = H^\top(HH^\top)^{-1}H.$$
--
--   Then the random vector $Hg \in \mathbb{R}^n$ and the random variable $Q_H(g)$ are independent.
--
--   Indeed, if the columns of $V\in\mathbb{R}^{k\times(k-n)}$ form an orthonormal basis of $\ker H$, then $Q_H(g) = \|V^\top g\|^2$, and the jointly Gaussian vectors $Hg$ and $V^\top g$ are uncorrelated because $HV = 0$, hence independent. In the analysis of an inverse Wishart matrix this makes the regression coefficients $(HH^\top)^{-1}Hg$ of one row on the others independent of its residual, conditionally on the other rows.
--
--   **Formalization Note.** Independence is `ProbabilityTheory.IndepFun` with respect to the product measure `Measure.pi fun _ => gaussianReal 0 1` on `Fin k → ℝ`.
-- source:
--   standard fact: uncorrelated components of a Gaussian vector are independent; for $g \sim N(0,I_k)$ and a matrix $V$ with orthonormal columns spanning $\ker H$, $\operatorname{Cov}(Hg, V^\top g) = HV = 0$; see R. J. Muirhead, Aspects of Multivariate Statistical Theory, Wiley 1982, Ch. 1 (multivariate normal distribution: independence of uncorrelated normal subvectors) [section from memory].

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem regression_residual_indep {n k : ℕ} (H : Matrix (Fin n) (Fin k) ℝ) (hH : H.rank = n) :
    IndepFun (fun g : Fin k → ℝ => H *ᵥ g)
      (fun g : Fin k → ℝ => g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))
      (Measure.pi fun _ : Fin k => gaussianReal 0 1) := by sorry

end GaussianMatrix
