-- Prove2me | Theorems.Thm_LG2021_Concentration_parameter_observation_bias_bounds
-- name    : LG2021.Concentration.parameter_observation_bias_bounds
-- status  : Proved
-- author  : @sim2000dg
-- created : 2026-11-14T15:58:37.205844+00:00
-- url     : https://prove2.me/theorems/98355c75-80b7-43e0-91c6-a13877bf3c5a
-- title:
--   Lemma 4 — scalar and directional Gaussian observation bias
-- statement:
--   Let $d,n$ be positive integers and $D\ge0$. Set
--   $$L=32\log\!\bigl(10^6(d+1)(D+1)(n+1)\bigr),\qquad
--   \lambda=(4\cdot10^5dL)^{-1},\qquad r=10^5d^2\sqrt{2L}.$$
--   Let $f:\mathbb R^d\to\mathbb R$ be $K$-Lipschitz, with $|f(0)|\le1$ and $K\le dD/r$. Let $\|z\|\le r/(2d)$ and $\|\eta\|\le1$. Draw $X$ from the standard Euclidean Gaussian, and then draw $Y$ from a measurable probability kernel $\kappa(X)$.
--
--   Assume that, for Gaussian-almost every $x$, the exponential moment $\mathbb E[\exp(Y^2/16)\mid X=x]$ is integrable and at most two. On the support of the published Gaussian truncation at $(\lambda,r,z)$, assume $\mathbb E[Y\mid X=x]=f(x)$. The conditional mean outside that support is unrestricted.
--
--   Let $A_{\lambda,r,z}(X)$ be the published truncated scalar likelihood-ratio coefficient, and let $B_{\lambda,r,z,\eta}(X)$ be its published directional gradient coefficient. For the Gaussian surrogate
--   $$g(z)=\mathbb E[f(X)]+\lambda^{-1}\bigl(\mathbb E[f((1-\lambda)X+\lambda z)]-\mathbb E[f(X)]\bigr),$$
--   both numerical bias estimates hold:
--   $$\bigl|\mathbb E[YA_{\lambda,r,z}(X)]-g(z)\bigr|\le\frac1{8rn},\qquad
--   \bigl|\mathbb E[YB_{\lambda,r,z,\eta}(X)]-Dg(z)[\eta]\bigr|\le\frac1{8rn}.$$
--   The expectations use the Gaussian/kernel joint measure.
--
--   This isolates the scalar and gradient bias bounds associated with Lemma 4(a,b) of Lattimore and György (COLT 2021, PMLR 134), using the formal proof's explicit parameter choices and a conditional observation-kernel formulation. Requiring the mean only where the truncation is active permits legal-query fallback outside the active Gaussian region. All coefficients and Gaussian objects are the existing published definitions. This node is a closed analytic ingredient in the dimension-dependent stochastic convex-bandit regret proof.
-- source:
--   Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, Proceedings of the 34th Conference on Learning Theory, Proceedings of Machine Learning Research 134:2938–2964, 2021. Lemma 4(a,b), printed p. 7, and Appendix D, printed pp. 20–22. Explicit numerical parameter and conditional observation-kernel formulation.

import Mathlib
import Definitions.Def_LG2021_GaussianEstimators

open LG2021 LG2021.Concentration MeasureTheory ProbabilityTheory

theorem LG2021.Concentration.parameter_observation_bias_bounds {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    {D : ℝ} (hD : 0 ≤ D) {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (hf0 : |f 0| ≤ 1)
    (hK : (K : ℝ) ≤ paperLipschitz d D (parameterLog d D n))
    (z η : Space d) (hz : ‖z‖ ≤ paperRadius d (parameterLog d D n) / (2 * (d : ℝ)))
    (hη : ‖η‖ ≤ 1) (κ : Kernel (Space d) ℝ) [IsMarkovKernel κ]
    (hobs : ∀ᵐ x ∂gaussian d, Integrable (fun y : ℝ => Real.exp (y ^ 2 / 16)) (κ x) ∧
      (∫ y : ℝ, Real.exp (y ^ 2 / 16) ∂κ x) ≤ 2)
    (hmean : ∀ᵐ x ∂gaussian d,
      truncation (paperLambda d (parameterLog d D n)) (paperRadius d (parameterLog d D n)) z x = 1 →
        (∫ y, y ∂κ x) = f x) :
    |(∫ p : Space d × ℝ, p.2 * scalarCoefficient (paperLambda d (parameterLog d D n))
        (paperRadius d (parameterLog d D n)) z p.1 ∂((gaussian d) ⊗ₘ κ)) -
      surrogate (paperLambda d (parameterLog d D n)) f z| ≤
        1 / (8 * paperRadius d (parameterLog d D n) * (n : ℝ)) ∧
    |(∫ p : Space d × ℝ, p.2 * directionalGradientCoefficient (paperLambda d (parameterLog d D n))
        (paperRadius d (parameterLog d D n)) z η p.1 ∂((gaussian d) ⊗ₘ κ)) -
      fderiv ℝ (surrogate (paperLambda d (parameterLog d D n)) f) z η| ≤
        1 / (8 * paperRadius d (parameterLog d D n) * (n : ℝ)) := by sorry
