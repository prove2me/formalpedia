-- Prove2me | Theorems.Thm_NonconvexAG_Stoch_eq_3_11_xstar_value
-- name    : NonconvexAG.Stoch.eq_3_11_xstar_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:23:10.0471+00:00
-- url     : https://prove2.me/theorems/85a2c10b-380e-427b-8137-c5036e89d371
-- title:
--   Expected optimality gap E[Ψ(x^ag_N) − Ψ(x*)] ≤ Γ_N(‖x_0 − x*‖²/(2λ_1) + σ²Σ L_Ψβ_k²/Γ_k) (p. 18)
-- statement:
--   In the setting of (3.11) — $\Psi$ convex and differentiable with $L_\Psi$-Lipschitz gradient ($L_\Psi>0$), a jointly measurable oracle satisfying Assumption 1 along the run with noise level $\sigma$, the RSAG method from $x_0$, $N\ge1$, and (2.10) for $k=1,\dots,N$ — let $x^*$ be a minimizer of $\Psi$ and assume (3.6) for $k=1,\dots,N$:
--   $$\alpha_k\lambda_k\le L_\Psi\beta_k^2,\qquad\beta_k<1/L_\Psi .$$
--   Then $\Psi(x^{ag}_N)$ is integrable and
--   $$\mathbb E\big[\Psi(x^{ag}_N)-\Psi(x^*)\big]\le\Gamma_N\Big(\frac{\|x_0-x^*\|^2}{2\lambda_1}+\sigma^2\sum_{k=1}^N\frac{L_\Psi\beta_k^2}{\Gamma_k}\Big).$$
--
--   Applied at every horizon $k\le N$ and averaged with the mass function (3.7), it gives (3.9).
--
--   **Formalization Note** The paper prints $\|x_0-x\|^2$ on the right; the display is the case $x=x^*$ of (3.11), so the Lean states $\|x_0-x^*\|^2$. Assumption 1 is in the conditional form.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 18, §3.1, display "It also follows from (3.11) and (3.6)"

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_Stoch_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace NonconvexAG.Stoch

open GhadimiLan.RSG (E)

/-- The bound on the expected optimality gap at `x^ag_N` (p. 18, display "It also follows from
(3.11) and (3.6)", with the printed `‖x₀ − x‖` read as `‖x₀ − x*‖`): for convex `Ψ` with a
minimizer `x*`, under Assumption 1 along the run (conditional form), (2.10) and (3.6) for
`k = 1, …, N` (`N ≥ 1`), `Ψ(x^ag_N)` is integrable and
`E[Ψ(x^ag_N) − Ψ(x*)] ≤ Γ_N (‖x₀ − x*‖²/(2λ₁) + σ² Σ_{k=1}^N L_Ψβₖ²/Γₖ)`. -/
theorem eq_3_11_xstar_value {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
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
    (h36 : ∀ k ∈ Finset.Icc 1 N, α k * lam k ≤ LΨ * β k ^ 2 ∧ β k < 1 / LΨ) :
    Integrable (fun ω => Ψ (xagSeq G α β lam x0 ξ N ω)) μ ∧
    ∫ ω, (Ψ (xagSeq G α β lam x0 ξ N ω) - Ψ xstar) ∂μ ≤
      NonconvexAG.Smooth.Gamma α N * (‖x0 - xstar‖ ^ 2 / (2 * lam 1)
        + σ ^ 2 * ∑ k ∈ Finset.Icc 1 N, LΨ * β k ^ 2 / NonconvexAG.Smooth.Gamma α k) := by sorry

end NonconvexAG.Stoch
