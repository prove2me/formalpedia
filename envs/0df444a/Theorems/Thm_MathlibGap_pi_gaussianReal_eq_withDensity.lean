-- Prove2me | Theorems.Thm_MathlibGap_pi_gaussianReal_eq_withDensity
-- name    : MathlibGap.pi_gaussianReal_eq_withDensity
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T22:12:34.447655+00:00
-- url     : https://prove2.me/theorems/eed15060-9bcb-530a-8bbe-22040c5a6d2a
-- title:
--   The standard Gaussian on $\mathbb R^k$ has density $(2\pi)^{-k/2}e^{-|x|^2/2}$
-- statement:
--   For every $k$, the law of $k$ independent standard normal variables, i.e. the product measure $N(0,1)^{\otimes k}$ on $\mathbb R^k$, is absolutely continuous with respect to Lebesgue measure with density
--   $$\varphi_k(x)=(2\pi)^{-k/2}\exp\Big(-\tfrac12\sum_{i=1}^k x_i^2\Big).$$
--
--   **Formalization Note** The product law is `Measure.pi (fun _ : Fin k => gaussianReal 0 1)` on `Fin k → ℝ` and the density is attached with `withDensity` and `ENNReal.ofReal`. For $k=0$ both sides are the unit mass.
-- source:
--   Wikipedia, Multivariate normal distribution, https://en.wikipedia.org/wiki/Multivariate_normal_distribution (accessed 2026-11-26), sections 'Definitions' > 'Standard normal random vector' and 'Density function' > 'Non-degenerate case' (density with Σ = I, μ = 0)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MathlibGap

theorem pi_gaussianReal_eq_withDensity (k : ℕ) :
    Measure.pi (fun _ : Fin k => gaussianReal 0 1) =
      (volume : Measure (Fin k → ℝ)).withDensity
        (fun x => ENNReal.ofReal ((2 * Real.pi) ^ (-(k : ℝ) / 2) * Real.exp (-(∑ i, x i ^ 2) / 2))) := by sorry

end MathlibGap
