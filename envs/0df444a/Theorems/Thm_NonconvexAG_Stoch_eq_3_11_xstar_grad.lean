-- Prove2me | Theorems.Thm_NonconvexAG_Stoch_eq_3_11_xstar_grad
-- name    : NonconvexAG.Stoch.eq_3_11_xstar_grad
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:23:21.906969+00:00
-- url     : https://prove2.me/theorems/f709b0b3-b3af-414a-a080-dd97344d7dec
-- title:
--   (3.11) at x = x* — Σ(β_k/Γ_k)(1 − L_Ψβ_k)E‖∇Ψ(x^md_k)‖² ≤ ‖x_0 − x*‖²/(2λ_1) + σ²Σ L_Ψβ_k²/Γ_k (p. 18)
-- statement:
--   In the setting of (3.11) — $\Psi$ convex and differentiable with $L_\Psi$-Lipschitz gradient ($L_\Psi>0$), a jointly measurable oracle satisfying Assumption 1 along the run with noise level $\sigma$, the RSAG method from $x_0$, $N\ge1$, and (2.10) and $\alpha_k\lambda_k\le L_\Psi\beta_k^2$ for $k=1,\dots,N$ — let $x^*$ be a minimizer of $\Psi$. Then each $\|\nabla\Psi(x^{md}_k)\|^2$ ($k\le N$) is integrable and
--   $$\sum_{k=1}^N\frac{\beta_k}{\Gamma_k}(1-L_\Psi\beta_k)\,\mathbb E\|\nabla\Psi(x^{md}_k)\|^2\le\frac{\|x_0-x^*\|^2}{2\lambda_1}+\sigma^2\sum_{k=1}^N\frac{L_\Psi\beta_k^2}{\Gamma_k}.$$
--
--   Dividing by $\sum_k\Gamma_k^{-1}\beta_k(1-L_\Psi\beta_k)$ and weighting by the mass function (3.7) gives (3.8).
--
--   **Formalization Note** Assumption 1 is in the conditional form (`GhadimiLan.RSG.AssumptionA1` along the middle points).
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 18, §3.1, display "Now, fixing x = x*"

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_Stoch_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace NonconvexAG.Stoch

open GhadimiLan.RSG (E)

/-- The display after (3.11) with `x = x*` (p. 18, "Now, fixing x = x*"): for convex `Ψ` with a
minimizer `x*`, under Assumption 1 along the run (conditional form), (2.10) and the first
relation of (3.6) for `k = 1, …, N` (`N ≥ 1`), each `‖∇Ψ(x^md_k)‖²` (`k ≤ N`) is integrable and
`Σ_{k=1}^N (βₖ/Γₖ)(1 − L_Ψβₖ) E‖∇Ψ(x^md_k)‖² ≤ ‖x₀ − x*‖²/(2λ₁) + σ² Σ_{k=1}^N L_Ψβₖ²/Γₖ`. -/
theorem eq_3_11_xstar_grad {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
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
    (h36 : ∀ k ∈ Finset.Icc 1 N, α k * lam k ≤ LΨ * β k ^ 2) :
    (∀ k ∈ Finset.Icc 1 N,
      Integrable (fun ω => ‖g (xmdSeq G α β lam x0 ξ k ω)‖ ^ 2) μ) ∧
    ∑ k ∈ Finset.Icc 1 N, β k / NonconvexAG.Smooth.Gamma α k * (1 - LΨ * β k) *
        ∫ ω, ‖g (xmdSeq G α β lam x0 ξ k ω)‖ ^ 2 ∂μ ≤
      ‖x0 - xstar‖ ^ 2 / (2 * lam 1)
        + σ ^ 2 * ∑ k ∈ Finset.Icc 1 N, LΨ * β k ^ 2 / NonconvexAG.Smooth.Gamma α k := by sorry

end NonconvexAG.Stoch
