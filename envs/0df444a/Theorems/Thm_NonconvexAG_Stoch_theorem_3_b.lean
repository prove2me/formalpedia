-- Prove2me | Theorems.Thm_NonconvexAG_Stoch_theorem_3_b
-- name    : NonconvexAG.Stoch.theorem_3_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:23:14.870149+00:00
-- url     : https://prove2.me/theorems/8c661aa6-6d8a-44a1-ac1c-88f9f7377a40
-- title:
--   Theorem 3 b) — RSAG on convex Ψ, (3.8) and (3.9) with the mass function (3.7)
-- statement:
--   Let $\Psi:\mathbb R^n\to\mathbb R$ be convex and differentiable with $L_\Psi$-Lipschitz gradient ($L_\Psi>0$), with a minimizer $x^*$. Let the stochastic oracle $G$ be jointly measurable and satisfy Assumption 1 along the run with noise level $\sigma$ (conditional unbiasedness given $\mathcal F_{k-1}$ and $\mathbb E\|\delta_k\|^2\le\sigma^2$ for $k\ge1$). Run the RSAG method (Algorithm 3) from $x_0$ with step sizes $\alpha_1=1$, $\alpha_k\in(0,1)$ ($k\ge2$), $\beta_k,\lambda_k>0$. Fix $N\ge1$ and suppose that, for $k=1,\dots,N$, (2.10) holds and
--   $$\alpha_k\lambda_k\le L_\Psi\beta_k^2,\qquad\beta_k<1/L_\Psi\qquad(3.6),$$
--   and let the termination index $R$, independent of the noise, have the mass function (3.7), $p_k=\Gamma_k^{-1}\beta_k(1-L_\Psi\beta_k)/\sum_{j=1}^N\Gamma_j^{-1}\beta_j(1-L_\Psi\beta_j)$. Then $\|\nabla\Psi(x^{md}_R)\|^2$ and $\Psi(x^{ag}_R)-\Psi(x^*)$ are integrable and
--   $$\mathbb E\big[\|\nabla\Psi(x^{md}_R)\|^2\big]\le\frac{(2\lambda_1)^{-1}\|x_0-x^*\|^2+L_\Psi\sigma^2\sum_{k=1}^N\Gamma_k^{-1}\beta_k^2}{\sum_{k=1}^N\Gamma_k^{-1}\beta_k(1-L_\Psi\beta_k)},$$
--   $$\mathbb E\big[\Psi(x^{ag}_R)-\Psi(x^*)\big]\le\frac{\sum_{k=1}^N\beta_k(1-L_\Psi\beta_k)\Big[(2\lambda_1)^{-1}\|x_0-x^*\|^2+L_\Psi\sigma^2\sum_{j=1}^k\Gamma_j^{-1}\beta_j^2\Big]}{\sum_{k=1}^N\Gamma_k^{-1}\beta_k(1-L_\Psi\beta_k)},$$
--   the expectations being over $R$ and $\xi_{[N]}$.
--
--   These are the convex guarantees of the method; Corollary 3 b) (pp. 18–19) specializes them to explicit step sizes.
--
--   **Formalization Note** Assumption 1 is in the conditional form (`GhadimiLan.RSG.AssumptionA1` along the middle points). (2.10) and (3.6) are stated on $\{1,\dots,N\}$. The independence of $R$ from the noise and $L_\Psi>0$ are explicit; integrability is part of the conclusion.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, pp. 15–16, Theorem 3 b), (3.6)–(3.9)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_Stoch_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace NonconvexAG.Stoch

open GhadimiLan.RSG (E)

/-- Theorem 3 b), pp. 15–16, (3.8) and (3.9): `Ψ` convex with a minimizer `x*`; under
Assumption 1 along the run (conditional form), (2.10) and (3.6) for `k = 1, …, N` (`N ≥ 1`), and
a termination index `R` with mass function (3.7), independent of the noise,
`‖∇Ψ(x^md_R)‖²` and `Ψ(x^ag_R) − Ψ(x*)` are integrable and
`E‖∇Ψ(x^md_R)‖² ≤ ((2λ₁)⁻¹‖x₀ − x*‖² + L_Ψσ² Σ_{k=1}^N Γₖ⁻¹βₖ²) / Σ_{k=1}^N Γₖ⁻¹βₖ(1 − L_Ψβₖ)`,
`E[Ψ(x^ag_R) − Ψ(x*)] ≤ Σ_{k=1}^N βₖ(1 − L_Ψβₖ)[(2λ₁)⁻¹‖x₀ − x*‖² + L_Ψσ² Σ_{j=1}^k Γⱼ⁻¹βⱼ²]
  / Σ_{k=1}^N Γₖ⁻¹βₖ(1 − L_Ψβₖ)`. -/
theorem theorem_3_b {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ) (hL : 0 < LΨ)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ) (σ : ℝ)
    (α β lam : ℕ → ℝ) (hstep : RSAGStepsizes α β lam) (x0 : E n)
    (hA1 : GhadimiLan.RSG.AssumptionA1 μ ℱ g G ξ (xmdSeq G α β lam x0 ξ) σ)
    (hconv : ConvexOn ℝ Set.univ Ψ) (xstar : E n) (hxstar : ∀ x, Ψ xstar ≤ Ψ x)
    (N : ℕ) (hN : 1 ≤ N)
    (h210 : ∀ k ∈ Finset.Icc 2 N,
      α k / (lam k * NonconvexAG.Smooth.Gamma α k) ≤ α (k - 1) / (lam (k - 1) * NonconvexAG.Smooth.Gamma α (k - 1)))
    (h36 : ∀ k ∈ Finset.Icc 1 N, α k * lam k ≤ LΨ * β k ^ 2 ∧ β k < 1 / LΨ)
    (R : Ω → ℕ) (hR : IsOutputIndex μ R N (pmfB LΨ α β N))
    (hRind : IndepFun R (fun ω k => ξ k ω) μ) :
    Integrable (fun ω => ‖g (xmdSeq G α β lam x0 ξ (R ω) ω)‖ ^ 2) μ ∧
      ∫ ω, ‖g (xmdSeq G α β lam x0 ξ (R ω) ω)‖ ^ 2 ∂μ ≤
        ((2 * lam 1)⁻¹ * ‖x0 - xstar‖ ^ 2
            + LΨ * σ ^ 2 * ∑ k ∈ Finset.Icc 1 N, (NonconvexAG.Smooth.Gamma α k)⁻¹ * β k ^ 2) /
          ∑ k ∈ Finset.Icc 1 N, (NonconvexAG.Smooth.Gamma α k)⁻¹ * β k * (1 - LΨ * β k) ∧
    Integrable (fun ω => Ψ (xagSeq G α β lam x0 ξ (R ω) ω) - Ψ xstar) μ ∧
      ∫ ω, (Ψ (xagSeq G α β lam x0 ξ (R ω) ω) - Ψ xstar) ∂μ ≤
        (∑ k ∈ Finset.Icc 1 N, β k * (1 - LΨ * β k) *
            ((2 * lam 1)⁻¹ * ‖x0 - xstar‖ ^ 2
              + LΨ * σ ^ 2 * ∑ j ∈ Finset.Icc 1 k, (NonconvexAG.Smooth.Gamma α j)⁻¹ * β j ^ 2)) /
          ∑ k ∈ Finset.Icc 1 N, (NonconvexAG.Smooth.Gamma α k)⁻¹ * β k * (1 - LΨ * β k) := by sorry

end NonconvexAG.Stoch
