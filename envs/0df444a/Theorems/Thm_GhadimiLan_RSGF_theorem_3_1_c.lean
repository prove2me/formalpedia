-- Prove2me | Theorems.Thm_GhadimiLan_RSGF_theorem_3_1_c
-- name    : GhadimiLan.RSGF.theorem_3_1_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:34.587207+00:00
-- url     : https://prove2.me/theorems/0ad2e89b-767c-467f-a83e-dd9b9995952a
-- title:
--   Theorem 3.1 c), (3.7), p. 15 — (1/µ²)E_u[{f(x+µu) − f(x)}²‖u‖²] ≤ (µ²/2)L²(n+6)³ + 2(n+4)‖∇f(x)‖²
-- statement:
--   Let $f : \mathbb R^n \to \mathbb R$ be differentiable with $L$-Lipschitz gradient, $L \ge 0$, let $\mu > 0$, and let $u$ be an $n$-dimensional standard Gaussian vector. Then for every $x \in \mathbb R^n$ the random variable $\{f(x+\mu u) - f(x)\}^2\|u\|^2$ is integrable and
--   $$
--   \frac{1}{\mu^2}\, \mathbb E_u\big[\{f(x+\mu u) - f(x)\}^2 \|u\|^2\big] \le \frac{\mu^2}{2} L^2 (n+6)^3 + 2(n+4)\|\nabla f(x)\|^2 .
--   $$
--
--   The left side is the second moment $\mathbb E_u\|g_\mu(x)\|^2$ of the Gaussian finite-difference estimator $g_\mu(x) = \frac{f(x+\mu u)-f(x)}{\mu}u$. The bound controls the variance of the RSGF estimator in the proof of Theorem 3.2, where it is applied to the sample functions $F(\cdot,\xi_k)$, which need not be convex.
--
--   **Formalization Note** No convexity is assumed. The platform theorem `RandomGradFree.Smooth.oracle_second_moment` has the same bound with an extra convexity hypothesis, so it is not this statement. The integrability of the integrand is part of the conclusion, so that the expectation is a genuine integral.
-- source:
--   Ghadimi & Lan, arXiv:1309.5549v1, Theorem 3.1 c), Eq. (3.7), p. 15

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

open MeasureTheory ProbabilityTheory

namespace GhadimiLan.RSGF

/-- Theorem 3.1 c), Eq. (3.7) (Ghadimi & Lan, arXiv:1309.5549v1, p. 15; due to Nesterov): for
`f ∈ C^{1,1}_L(ℝⁿ)` (no convexity), `μs > 0` (the paper's `µ`) and `u` an `n`-dimensional
standard Gaussian vector, `(1/µ²) E_u[{f(x + µu) − f(x)}² ‖u‖²] ≤ (µ²/2) L² (n+6)³ + 2(n+4)‖∇f(x)‖²`
for every `x`. The integrability of the integrand is part of the claim. -/
theorem theorem_3_1_c {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hdiff : Differentiable ℝ f) (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (μs : ℝ) (hμs : 0 < μs) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun u => (f (x + μs • u) - f x) ^ 2 * ‖u‖ ^ 2)
        (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
      1 / μs ^ 2 * ∫ u, (f (x + μs • u) - f x) ^ 2 * ‖u‖ ^ 2
          ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
        μs ^ 2 / 2 * L ^ 2 * ((n : ℝ) + 6) ^ 3 + 2 * ((n : ℝ) + 4) * ‖gradient f x‖ ^ 2 := by sorry

end GhadimiLan.RSGF
