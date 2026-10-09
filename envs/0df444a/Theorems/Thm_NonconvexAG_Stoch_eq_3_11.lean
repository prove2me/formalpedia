-- Prove2me | Theorems.Thm_NonconvexAG_Stoch_eq_3_11
-- name    : NonconvexAG.Stoch.eq_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:24:41.16583+00:00
-- url     : https://prove2.me/theorems/44db9365-144d-4c0a-86bf-7efbf59a2c77
-- title:
--   (3.11) — (1/Γ_N)E[Ψ(x^ag_N) − Ψ(x)] ≤ ‖x_0 − x‖²/(2λ_1) − Σ(β_k/Γ_k)(1 − L_Ψβ_k)E‖∇Ψ(x^md_k)‖² + σ²Σ L_Ψβ_k²/Γ_k
-- statement:
--   Let $\Psi:\mathbb R^n\to\mathbb R$ be convex and differentiable with $L_\Psi$-Lipschitz gradient ($L_\Psi>0$), let the oracle $G$ be jointly measurable and satisfy Assumption 1 along the run with noise level $\sigma$ (conditional unbiasedness given $\mathcal F_{k-1}$ and $\mathbb E\|\delta_k\|^2\le\sigma^2$ for $k\ge1$), and run the RSAG method (Algorithm 3) from $x_0$ with step sizes $\alpha_1=1$, $\alpha_k\in(0,1)$ ($k\ge2$), $\beta_k,\lambda_k>0$. Fix $N\ge1$ and suppose that for $k=1,\dots,N$
--   $$\frac{\alpha_1}{\lambda_1\Gamma_1}\ge\frac{\alpha_2}{\lambda_2\Gamma_2}\ge\dots\ge\frac{\alpha_N}{\lambda_N\Gamma_N}\quad(2.10),\qquad\alpha_k\lambda_k\le L_\Psi\beta_k^2 .$$
--   Then for every $x\in\mathbb R^n$, the quantities $\|\nabla\Psi(x^{md}_k)\|^2$ ($k\le N$) and $\Psi(x^{ag}_N)$ are integrable and
--   $$\frac{1}{\Gamma_N}\mathbb E\big[\Psi(x^{ag}_N)-\Psi(x)\big]\le\frac{\|x_0-x\|^2}{2\lambda_1}-\sum_{k=1}^N\frac{\beta_k}{\Gamma_k}(1-L_\Psi\beta_k)\,\mathbb E\|\nabla\Psi(x^{md}_k)\|^2+\sigma^2\sum_{k=1}^N\frac{L_\Psi\beta_k^2}{\Gamma_k}.$$
--
--   This is the central estimate of the convex case: from it follow both the gradient bound (3.8) and the optimality-gap bound (3.9).
--
--   **Formalization Note** Assumption 1 is the published `GhadimiLan.RSG.AssumptionA1` along the middle points, in the conditional form the paper's martingale-difference argument uses. Only the first relation of (3.6) is assumed, as in the paper's derivation; (2.10) is stated on $\{1,\dots,N\}$. Integrability is part of the conclusion.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, pp. 17–18, (3.11)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_Stoch_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace NonconvexAG.Stoch

open GhadimiLan.RSG (E)

/-- (3.11), pp. 17–18: for convex `Ψ`, under Assumption 1 along the run (conditional form),
(2.10) for `k = 1, …, N` and the first relation `αₖλₖ ≤ L_Ψβₖ²` of (3.6) for `k = 1, …, N`
(`N ≥ 1`), for every `x ∈ ℝⁿ` the quantities `‖∇Ψ(x^md_k)‖²` (`k ≤ N`) and `Ψ(x^ag_N)` are
integrable and
`(1/Γ_N) E[Ψ(x^ag_N) − Ψ(x)] ≤ ‖x₀ − x‖²/(2λ₁) − Σ_{k=1}^N (βₖ/Γₖ)(1 − L_Ψβₖ) E‖∇Ψ(x^md_k)‖²
  + σ² Σ_{k=1}^N L_Ψβₖ²/Γₖ`. -/
theorem eq_3_11 {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ) (hL : 0 < LΨ)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ) (σ : ℝ)
    (α β lam : ℕ → ℝ) (hstep : RSAGStepsizes α β lam) (x0 : E n)
    (hA1 : GhadimiLan.RSG.AssumptionA1 μ ℱ g G ξ (xmdSeq G α β lam x0 ξ) σ)
    (hconv : ConvexOn ℝ Set.univ Ψ) (N : ℕ) (hN : 1 ≤ N)
    (h210 : ∀ k ∈ Finset.Icc 2 N,
      α k / (lam k * NonconvexAG.Smooth.Gamma α k) ≤ α (k - 1) / (lam (k - 1) * NonconvexAG.Smooth.Gamma α (k - 1)))
    (h36 : ∀ k ∈ Finset.Icc 1 N, α k * lam k ≤ LΨ * β k ^ 2) (x : E n) :
    (∀ k ∈ Finset.Icc 1 N,
      Integrable (fun ω => ‖g (xmdSeq G α β lam x0 ξ k ω)‖ ^ 2) μ) ∧
    Integrable (fun ω => Ψ (xagSeq G α β lam x0 ξ N ω)) μ ∧
    1 / NonconvexAG.Smooth.Gamma α N * ∫ ω, (Ψ (xagSeq G α β lam x0 ξ N ω) - Ψ x) ∂μ ≤
      ‖x0 - x‖ ^ 2 / (2 * lam 1)
        - ∑ k ∈ Finset.Icc 1 N, β k / NonconvexAG.Smooth.Gamma α k * (1 - LΨ * β k) *
            ∫ ω, ‖g (xmdSeq G α β lam x0 ξ k ω)‖ ^ 2 ∂μ
        + σ ^ 2 * ∑ k ∈ Finset.Icc 1 N, LΨ * β k ^ 2 / NonconvexAG.Smooth.Gamma α k := by sorry

end NonconvexAG.Stoch
