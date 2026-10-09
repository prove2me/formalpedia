-- Prove2me | Theorems.Thm_NonconvexAG_Stoch_theorem_3
-- name    : NonconvexAG.Stoch.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:23:16.527783+00:00
-- url     : https://prove2.me/theorems/8be4428f-2fc8-44bf-9127-d3232b3f3e44
-- title:
--   Theorem 3 — the randomized stochastic AG method, parts a) (3.5) and b) (3.8)–(3.9)
-- statement:
--   Let $\Psi:\mathbb R^n\to\mathbb R$ be differentiable with $L_\Psi$-Lipschitz gradient, $L_\Psi>0$. A stochastic first-order oracle returns, at its $k$-th call at the input $x$, the vector $G(x,\xi_k)$, where $\xi_1,\xi_2,\dots$ are random variables on a probability space and $G$ is jointly measurable. Run the **randomized stochastic accelerated gradient (RSAG) method** (Algorithm 3): from $x_0$, with step sizes $\alpha_1=1$, $\alpha_k\in(0,1)$ ($k\ge2$), $\beta_k>0$, $\lambda_k>0$, set $x^{ag}_0=x_0$ and for $k\ge1$
--   $$x^{md}_k=(1-\alpha_k)x^{ag}_{k-1}+\alpha_kx_{k-1},\qquad x_k=x_{k-1}-\lambda_kG(x^{md}_k,\xi_k),\qquad x^{ag}_k=x^{md}_k-\beta_kG(x^{md}_k,\xi_k);$$
--   the output is $(x^{md}_R,x^{ag}_R)$ for a random index $R\in\{1,\dots,N\}$ drawn independently of the noise. Assume **Assumption 1** along the run with noise level $\sigma$: for a filtration $(\mathcal F_k)$ to which the noise is adapted and every $k\ge1$,
--   $$\mathbb E\big[G(x^{md}_k,\xi_k)\,\big|\,\mathcal F_{k-1}\big]=\nabla\Psi(x^{md}_k)\ \text{a.s.},\qquad\mathbb E\|G(x^{md}_k,\xi_k)-\nabla\Psi(x^{md}_k)\|^2\le\sigma^2 .$$
--   Let $\Gamma_k$ be (2.6) and $C_k$ (2.7), and fix $N\ge1$.
--
--   1. If $\Psi$ is bounded below with $\Psi^*=\inf\Psi$, $C_k>0$ for $k=1,\dots,N$, and $\Pr\{R=k\}=\lambda_kC_k/\sum_{j=1}^N\lambda_jC_j$ (3.4), then $\|\nabla\Psi(x^{md}_R)\|^2$ is integrable and
--   $$\mathbb E\big[\|\nabla\Psi(x^{md}_R)\|^2\big]\le\frac{1}{\sum_{k=1}^N\lambda_kC_k}\Big[\Psi(x_0)-\Psi^*+\frac{L_\Psi\sigma^2}{2}\sum_{k=1}^N\lambda_k^2\Big(1+\frac{(\lambda_k-\beta_k)^2}{\alpha_k\Gamma_k\lambda_k^2}\sum_{\tau=k}^N\Gamma_\tau\Big)\Big].\qquad(3.5)$$
--   2. If $\Psi$ is convex with a minimizer $x^*$, (2.10) holds and $\alpha_k\lambda_k\le L_\Psi\beta_k^2$, $\beta_k<1/L_\Psi$ (3.6) for $k=1,\dots,N$, and $\Pr\{R=k\}=\Gamma_k^{-1}\beta_k(1-L_\Psi\beta_k)/\sum_{j=1}^N\Gamma_j^{-1}\beta_j(1-L_\Psi\beta_j)$ (3.7), then $\|\nabla\Psi(x^{md}_R)\|^2$ and $\Psi(x^{ag}_R)-\Psi(x^*)$ are integrable and
--   $$\mathbb E\big[\|\nabla\Psi(x^{md}_R)\|^2\big]\le\frac{(2\lambda_1)^{-1}\|x_0-x^*\|^2+L_\Psi\sigma^2\sum_{k=1}^N\Gamma_k^{-1}\beta_k^2}{\sum_{k=1}^N\Gamma_k^{-1}\beta_k(1-L_\Psi\beta_k)},\qquad(3.8)$$
--   $$\mathbb E\big[\Psi(x^{ag}_R)-\Psi(x^*)\big]\le\frac{\sum_{k=1}^N\beta_k(1-L_\Psi\beta_k)\Big[(2\lambda_1)^{-1}\|x_0-x^*\|^2+L_\Psi\sigma^2\sum_{j=1}^k\Gamma_j^{-1}\beta_j^2\Big]}{\sum_{k=1}^N\Gamma_k^{-1}\beta_k(1-L_\Psi\beta_k)}.\qquad(3.9)$$
--
--   The expectations are over both $R$ and $\xi_{[N]}=(\xi_1,\dots,\xi_N)$. One stochastic method thus has a nonconvex guarantee for the expected squared gradient and, when $\Psi$ is convex, the optimal rate of stochastic convex optimization.
--
--   **Formalization Note** The paper states Assumption 1 unconditionally, (1.4)–(1.5), and stresses that the $\xi_k$ need not be independent; its proof uses that the error terms are martingale differences. The Lean uses the conditional form along the run (the published `GhadimiLan.RSG.AssumptionA1`, applied to the middle points), which is what the proof uses and holds in the independent case. The independence of $R$ from the noise sequence, the joint measurability of $G$ and $L_\Psi>0$ are explicit; (2.7), (2.10) and (3.6) are required for $k=1,\dots,N$. Each expectation comes with the integrability of its integrand, since Lean's integral of a non-integrable function is $0$. The two parts quantify over their own termination index $R$, because they use different mass functions.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, pp. 15–16, Theorem 3 (3.4)–(3.9)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_Stoch_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace NonconvexAG.Stoch

open GhadimiLan.RSG (E)

/-- Theorem 3 (Ghadimi–Lan, arXiv:1310.3787v1, pp. 15–16): the RSAG method (Algorithm 3) under
Assumption 1 (conditional form along the run), for every `N ≥ 1`.
a) If `Ψ` is bounded below, (2.7) holds for `k = 1, …, N` and `R` has the mass function (3.4)
   and is independent of the noise, then (3.5) holds.
b) If `Ψ` is convex with a minimizer `x*`, (2.10) and (3.6) hold for `k = 1, …, N` and `R` has
   the mass function (3.7) and is independent of the noise, then (3.8) and (3.9) hold.
Every expectation is over `R` and `ξ_[N]` and comes with the integrability of its integrand. -/
theorem theorem_3 {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ) (hL : 0 < LΨ)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ) (σ : ℝ)
    (α β lam : ℕ → ℝ) (hstep : RSAGStepsizes α β lam) (x0 : E n)
    (hA1 : GhadimiLan.RSG.AssumptionA1 μ ℱ g G ξ (xmdSeq G α β lam x0 ξ) σ)
    (N : ℕ) (hN : 1 ≤ N) :
    (BddBelow (Set.range Ψ) → (∀ k ∈ Finset.Icc 1 N, 0 < NonconvexAG.Smooth.C LΨ α β lam N k) →
      ∀ R : Ω → ℕ, IsOutputIndex μ R N (pmfA LΨ α β lam N) →
        IndepFun R (fun ω k => ξ k ω) μ →
      Integrable (fun ω => ‖g (xmdSeq G α β lam x0 ξ (R ω) ω)‖ ^ 2) μ ∧
      ∫ ω, ‖g (xmdSeq G α β lam x0 ξ (R ω) ω)‖ ^ 2 ∂μ ≤
        1 / (∑ k ∈ Finset.Icc 1 N, lam k * NonconvexAG.Smooth.C LΨ α β lam N k) *
          (Ψ x0 - (⨅ x, Ψ x) + LΨ * σ ^ 2 / 2 * ∑ k ∈ Finset.Icc 1 N,
            lam k ^ 2 * (1 + (lam k - β k) ^ 2 / (α k * NonconvexAG.Smooth.Gamma α k * lam k ^ 2) *
              ∑ τ ∈ Finset.Icc k N, NonconvexAG.Smooth.Gamma α τ))) ∧
    (∀ xstar : E n, ConvexOn ℝ Set.univ Ψ → (∀ x, Ψ xstar ≤ Ψ x) →
      (∀ k ∈ Finset.Icc 2 N,
        α k / (lam k * NonconvexAG.Smooth.Gamma α k) ≤ α (k - 1) / (lam (k - 1) * NonconvexAG.Smooth.Gamma α (k - 1))) →
      (∀ k ∈ Finset.Icc 1 N, α k * lam k ≤ LΨ * β k ^ 2 ∧ β k < 1 / LΨ) →
      ∀ R : Ω → ℕ, IsOutputIndex μ R N (pmfB LΨ α β N) →
        IndepFun R (fun ω k => ξ k ω) μ →
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
          ∑ k ∈ Finset.Icc 1 N, (NonconvexAG.Smooth.Gamma α k)⁻¹ * β k * (1 - LΨ * β k)) := by sorry

end NonconvexAG.Stoch
