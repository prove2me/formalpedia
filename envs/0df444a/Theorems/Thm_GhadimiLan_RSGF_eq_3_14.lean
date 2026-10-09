-- Prove2me | Theorems.Thm_GhadimiLan_RSGF_eq_3_14
-- name    : GhadimiLan.RSGF.eq_3_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:19:10.310902+00:00
-- url     : https://prove2.me/theorems/71af9569-1b09-4f51-9bbf-44eeead7bf51
-- title:
--   (3.14), p. 16 — E_{ξ,u}[G_µ(x, ξ, u)] = ∇f_µ(x): the zeroth-order estimator is unbiased for ∇f_µ
-- statement:
--   Assume the standing assumptions of Section 3: Assumptions A1 and A3 hold for the integrand $F$ and the distribution $P$, and $F(\cdot,\xi) \in \mathcal C^{1,1}_L$ almost surely, with $L > 0$. Let $f(x) = \mathbb E[F(x,\xi)]$, let $\mu > 0$, and let $f_\mu$ be the Gaussian smoothing of $f$. Let $\xi \sim P$ and let $u$ be an independent $n$-dimensional standard Gaussian vector. Then for every $x \in \mathbb R^n$ the estimator $G_\mu(x,\xi,u)$ of (3.12) is integrable and
--   $$
--   \mathbb E_{\xi,u}[G_\mu(x,\xi,u)] = \nabla f_\mu(x).
--   $$
--
--   So $G_\mu(x,\xi,u)$ is an unbiased estimator of the gradient of the smoothed objective. This is what makes the RSGF method a stochastic gradient method for $f_\mu$.
--
--   **Formalization Note** The joint expectation over $(\xi,u)$ is the integral against the product measure $P \otimes \mathcal N(0,I_n)$. The smoothing parameter is `μs`.
-- source:
--   Ghadimi & Lan, arXiv:1309.5549v1, Eq. (3.14), p. 16

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing
import Definitions.Def_GhadimiLan_RSGF_Model

open MeasureTheory ProbabilityTheory

namespace GhadimiLan.RSGF

/-- Eq. (3.14) (Ghadimi & Lan, arXiv:1309.5549v1, p. 16): under the standing assumptions of §3
(`SZOAssumptions`: A1, A3, `F(·, ξ) ∈ C^{1,1}_L` a.s.) and for `μs > 0` (the paper's `µ`), the
zeroth-order estimator `G_µ(x, ξ, u)` of (3.12), with `ξ ~ P` and `u` an independent standard
Gaussian vector, is integrable and unbiased for the gradient of the Gaussian smoothing
`f_µ` of `f = objective P F`: `E_{ξ,u}[G_µ(x, ξ, u)] = ∇f_µ(x)` for every `x`. -/
theorem eq_3_14 {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (P : Measure Ξ) [IsProbabilityMeasure P]
    (F : EuclideanSpace ℝ (Fin n) → Ξ → ℝ) (L σ μs : ℝ) (hL : 0 < L) (hμs : 0 < μs)
    (hF : SZOAssumptions P F L σ) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun p : Ξ × EuclideanSpace ℝ (Fin n) => szoGrad F μs x p.1 p.2)
        (P.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
      ∫ p, szoGrad F μs x p.1 p.2 ∂(P.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) =
        gradient (RandomGradFree.Shared.smoothing (objective P F) μs) x := by sorry

end GhadimiLan.RSGF
