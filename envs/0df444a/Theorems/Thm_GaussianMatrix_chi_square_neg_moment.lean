-- Prove2me | Theorems.Thm_GaussianMatrix_chi_square_neg_moment
-- name    : GaussianMatrix.chi_square_neg_moment
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T04:58:21.319178+00:00
-- url     : https://prove2.me/theorems/96b23ddd-3a67-4c70-94ad-e194fc2bc324
-- title:
--   Negative moments of the chi-square distribution: $\mathbb{E}[\Xi^{-q}] = \Gamma(d/2-q)/(2^q\Gamma(d/2))$ for $0 \le q < d/2$
-- statement:
--   Let $d \ge 1$ and let $x = (x_1,\dots,x_d)$ have independent standard normal coordinates, so that $\Xi = \sum_{j=1}^d x_j^2$ is a chi-square variable with $d$ degrees of freedom. For every real exponent $q$ with $0 \le q < d/2$, the random variable $\Xi^{-q}$ is integrable and
--
--   $$\mathbb{E}\big[\Xi^{-q}\big] \;=\; \int_{\mathbb{R}^d} \Big(\sum_{j=1}^d x_j^2\Big)^{-q} d\gamma_d(x) \;=\; \frac{\Gamma(d/2 - q)}{2^q\,\Gamma(d/2)},$$
--
--   where $\gamma_d$ is the standard Gaussian measure on $\mathbb{R}^d$ and $\Gamma$ is Euler's Gamma function.
--
--   This is the negative-moment half of HMT's Proposition A.8. It is the exact formula from which the $L^q$ bound $\mathbb{E}_q(\Xi^{-1}) < 3/d$ of HMT Lemma A.10 is derived, and that bound drives the tail estimate for $\|G^\dagger\|_F^2$.
--
--   **Formalization Note.** The integrand is written $((\sum_j x_j^2)^{-1})^q$ with the real power `Real.rpow`; since $0^{-1}=0$ in Lean it is defined everywhere, and the event $\Xi=0$ is null. The condition $q < d/2$ forces $d \ge 1$; for $q=0$ both sides equal $1$. For $q \ge d/2$ the integral diverges.
-- source:
--   N. Halko, P.-G. Martinsson, J. A. Tropp, Finding structure with randomness: Probabilistic algorithms for constructing approximate matrix decompositions, SIAM Review 53(2) (2011), 217–288 (arXiv:0909.4061), Proposition A.8 (arXiv version p. 66), the formula $\mathbb{E}\,\Xi^{-q} = \Gamma(k/2-q)/(2^q\Gamma(k/2))$ for $0 \le q < k/2$.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem chi_square_neg_moment {d : ℕ} (q : ℝ) (hq : 0 ≤ q) (hqd : q < (d : ℝ) / 2) :
    Integrable (fun x : Fin d → ℝ => ((∑ j, x j ^ 2)⁻¹) ^ q)
        (Measure.pi fun _ : Fin d => gaussianReal 0 1) ∧
    ∫ x, ((∑ j, x j ^ 2)⁻¹) ^ q ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1)
      = Real.Gamma ((d : ℝ) / 2 - q) / (2 ^ q * Real.Gamma ((d : ℝ) / 2)) := by sorry

end GaussianMatrix
