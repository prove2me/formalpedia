-- Prove2me | Theorems.Thm_NonconvexAG_Stoch_eq_expected
-- name    : NonconvexAG.Stoch.eq_expected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:23:49.199471+00:00
-- url     : https://prove2.me/theorems/504702f0-580a-40de-886b-e785aee1e851
-- title:
--   Expected RSAG descent Σ λ_kC_k E‖∇Ψ(x^md_k)‖² ≤ Ψ(x_0) − E Ψ(x_N) + (L_Ψσ²/2) Σ … (p. 17)
-- statement:
--   Let $\Psi:\mathbb R^n\to\mathbb R$ be differentiable with $L_\Psi$-Lipschitz gradient, let the oracle $G$ be jointly measurable, and run the RSAG method (Algorithm 3) from $x_0$ with step sizes $\alpha_1=1$, $\alpha_k\in(0,1)$ ($k\ge2$), $\beta_k,\lambda_k>0$. Suppose Assumption 1 holds along the run with noise level $\sigma$: for a filtration $(\mathcal F_k)$ to which the noise is adapted and every $k\ge1$,
--   $$\mathbb E\big[G(x^{md}_k,\xi_k)\,\big|\,\mathcal F_{k-1}\big]=\nabla\Psi(x^{md}_k)\ \text{a.s.},\qquad\mathbb E\|G(x^{md}_k,\xi_k)-\nabla\Psi(x^{md}_k)\|^2\le\sigma^2 .$$
--   Then for every $N\ge1$ the quantities $\|\nabla\Psi(x^{md}_k)\|^2$ ($k=1,\dots,N$) and $\Psi(x_N)$ are integrable and
--   $$\sum_{k=1}^N\lambda_kC_k\,\mathbb E\|\nabla\Psi(x^{md}_k)\|^2\le\Psi(x_0)-\mathbb E[\Psi(x_N)]+\frac{L_\Psi\sigma^2}{2}\sum_{k=1}^N\lambda_k^2\Big(1+\frac{(\lambda_k-\beta_k)^2}{\alpha_k\Gamma_k\lambda_k^2}\sum_{\tau=k}^N\Gamma_\tau\Big),$$
--   with $C_k$ the constants (2.7) for the horizon $N$.
--
--   This is the expected form of the summed descent inequality: the martingale terms have mean zero and the variance terms are bounded by $\sigma^2$. No sign condition on $C_k$ is needed.
--
--   **Formalization Note** The paper writes $\Psi(x_0)-\Psi(x_N)$ on the right; since $x_N$ is random, the Lean writes its expectation, which is what taking expectations of the pathwise inequality gives. Assumption 1 is the published `GhadimiLan.RSG.AssumptionA1` along the middle points $x^{md}_k$, in the conditional form the paper's martingale-difference argument uses; it holds in particular when the $\xi_k$ are independent and satisfy (1.4)–(1.5). Integrability is part of the conclusion, since Lean's integral of a non-integrable function is $0$.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 17, §3.1, display after "is a martingale difference"

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_Stoch_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace NonconvexAG.Stoch

open GhadimiLan.RSG (E)

/-- The expected descent inequality of the proof of Theorem 3 a) (p. 17, display after "is a
martingale difference"): under Assumption 1 along the run (conditional form), for every `N ≥ 1`
the quantities `‖∇Ψ(x^md_k)‖²` (`k = 1, …, N`) and `Ψ(x_N)` are integrable and
`Σ_{k=1}^N λₖCₖ E‖∇Ψ(x^md_k)‖² ≤ Ψ(x₀) − E[Ψ(x_N)]
  + (L_Ψσ²/2) Σ_{k=1}^N λₖ²(1 + ((λₖ − βₖ)²/(αₖΓₖλₖ²)) Σ_{τ=k}^N Γ_τ)`. -/
theorem eq_expected {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ) (σ : ℝ)
    (α β lam : ℕ → ℝ) (hstep : RSAGStepsizes α β lam) (x0 : E n)
    (hA1 : GhadimiLan.RSG.AssumptionA1 μ ℱ g G ξ (xmdSeq G α β lam x0 ξ) σ)
    (N : ℕ) (hN : 1 ≤ N) :
    (∀ k ∈ Finset.Icc 1 N,
      Integrable (fun ω => ‖g (xmdSeq G α β lam x0 ξ k ω)‖ ^ 2) μ) ∧
    Integrable (fun ω => Ψ (xSeq G α β lam x0 ξ N ω)) μ ∧
    ∑ k ∈ Finset.Icc 1 N,
        lam k * NonconvexAG.Smooth.C LΨ α β lam N k * ∫ ω, ‖g (xmdSeq G α β lam x0 ξ k ω)‖ ^ 2 ∂μ ≤
      Ψ x0 - ∫ ω, Ψ (xSeq G α β lam x0 ξ N ω) ∂μ
        + LΨ * σ ^ 2 / 2 * ∑ k ∈ Finset.Icc 1 N,
            lam k ^ 2 * (1 + (lam k - β k) ^ 2 / (α k * NonconvexAG.Smooth.Gamma α k * lam k ^ 2) *
              ∑ τ ∈ Finset.Icc k N, NonconvexAG.Smooth.Gamma α τ) := by sorry

end NonconvexAG.Stoch
