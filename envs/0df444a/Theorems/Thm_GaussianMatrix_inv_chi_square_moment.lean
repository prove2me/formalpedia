-- Prove2me | Theorems.Thm_GaussianMatrix_inv_chi_square_moment
-- name    : GaussianMatrix.inv_chi_square_moment
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T03:41:26.20295+00:00
-- url     : https://prove2.me/theorems/cc098a56-87e1-495a-93a5-bbf055267d0d
-- title:
--   Inverse moment of the chi-square distribution: $\mathbb{E}[1/\chi^2_d] = 1/(d-2)$ for $d \ge 3$
-- statement:
--   Let $d \ge 3$ and let $x = (x_1, \dots, x_d)$ have independent standard normal coordinates, so that $\Xi = \sum_{j=1}^d x_j^2$ has the chi-square distribution with $d$ degrees of freedom. Then $\Xi^{-1}$ is integrable and
--
--   $$\mathbb{E}\big[\Xi^{-1}\big] \;=\; \int_{\mathbb{R}^d} \Big(\sum_{j=1}^d x_j^2\Big)^{-1} \, d\gamma_d(x) \;=\; \frac{\Gamma(d/2 - 1)}{2\,\Gamma(d/2)} \;=\; \frac{1}{d-2},$$
--
--   where $\gamma_d$ is the standard Gaussian measure on $\mathbb{R}^d$.
--
--   This one-dimensional density computation supplies the constant $1/(k-r-1)$ in the formula $\mathbb{E}(GG^\top)^{-1} = I/(k-r-1)$ for an $r \times k$ standard Gaussian matrix, applied with $d = k - r + 1$ degrees of freedom.
--
--   **Formalization Note.** Since Lean's $0^{-1} = 0$, the integrand is defined everywhere; the event $\Xi = 0$ is Gaussian-null anyway. The hypothesis $d \ge 3$ is sharp: for $d \le 2$ the integral diverges.
-- source:
--   N. Halko, P.-G. Martinsson, J. A. Tropp, Finding structure with randomness, SIAM Review 53(2), 2011, Proposition A.8 (and the proof of Proposition A.5).

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem inv_chi_square_moment {d : ℕ} (hd : 3 ≤ d) :
    Integrable (fun x : Fin d → ℝ => (∑ j, x j ^ 2)⁻¹)
        (Measure.pi fun _ : Fin d => gaussianReal 0 1) ∧
    ∫ x, (∑ j, x j ^ 2)⁻¹ ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) = 1 / ((d : ℝ) - 2) := by sorry

end GaussianMatrix
