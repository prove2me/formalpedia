-- Prove2me | Theorems.Thm_NonconvexAG_Stoch_theorem_3_a
-- name    : NonconvexAG.Stoch.theorem_3_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:23:02.690252+00:00
-- url     : https://prove2.me/theorems/37523f6d-b73c-429f-bcde-7969db381bf4
-- title:
--   Theorem 3 a) — RSAG on nonconvex Ψ, (3.5) with the mass function (3.4)
-- statement:
--   Let $\Psi:\mathbb R^n\to\mathbb R$ be differentiable with $L_\Psi$-Lipschitz gradient ($L_\Psi>0$) and bounded below, with $\Psi^*=\inf_x\Psi(x)$. Let the stochastic oracle $G$ be jointly measurable and satisfy Assumption 1 along the run with noise level $\sigma$: for a filtration $(\mathcal F_k)$ to which the noise is adapted and every $k\ge1$,
--   $$\mathbb E\big[G(x^{md}_k,\xi_k)\,\big|\,\mathcal F_{k-1}\big]=\nabla\Psi(x^{md}_k)\ \text{a.s.},\qquad\mathbb E\|G(x^{md}_k,\xi_k)-\nabla\Psi(x^{md}_k)\|^2\le\sigma^2 .$$
--   Run the RSAG method (Algorithm 3) from $x_0$ with step sizes $\alpha_1=1$, $\alpha_k\in(0,1)$ ($k\ge2$), $\beta_k,\lambda_k>0$. Fix $N\ge1$, suppose $C_k>0$ for $k=1,\dots,N$ (2.7), and let the termination index $R$, independent of the noise, have the mass function (3.4), $p_k=\lambda_kC_k/\sum_{j=1}^N\lambda_jC_j$. Then $\|\nabla\Psi(x^{md}_R)\|^2$ is integrable and
--   $$\mathbb E\big[\|\nabla\Psi(x^{md}_R)\|^2\big]\le\frac{1}{\sum_{k=1}^N\lambda_kC_k}\Big[\Psi(x_0)-\Psi^*+\frac{L_\Psi\sigma^2}{2}\sum_{k=1}^N\lambda_k^2\Big(1+\frac{(\lambda_k-\beta_k)^2}{\alpha_k\Gamma_k\lambda_k^2}\sum_{\tau=k}^N\Gamma_\tau\Big)\Big],$$
--   where the expectation is over $R$ and $\xi_{[N]}=(\xi_1,\dots,\xi_N)$.
--
--   This is the nonconvex guarantee of the randomized stochastic AG method; Corollary 3 a) (p. 18) specializes it to explicit step sizes, giving a bound of order $1/N+\sigma/\sqrt N$.
--
--   **Formalization Note** Assumption 1 is stated in the conditional form used by the proof (the published `GhadimiLan.RSG.AssumptionA1` along the middle points); the paper explicitly allows dependent $\xi_k$, and the conditional form holds in the independent case. $\Psi^*$ is the infimum of $\Psi$, finite by `BddBelow`. The independence of $R$ from the noise sequence and $L_\Psi>0$ are explicit. Integrability of $\|\nabla\Psi(x^{md}_R)\|^2$ is part of the conclusion.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 15, Theorem 3 a), (3.4)–(3.5)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_Stoch_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace NonconvexAG.Stoch

open GhadimiLan.RSG (E)

/-- Theorem 3 a), p. 15, (3.5): `Ψ` bounded below with `Ψ* = inf Ψ`; under Assumption 1 along
the run (conditional form), (2.7) (`Cₖ > 0`) for `k = 1, …, N` (`N ≥ 1`), and a termination
index `R` with mass function (3.4), independent of the noise, `‖∇Ψ(x^md_R)‖²` is integrable and
`E‖∇Ψ(x^md_R)‖² ≤ (1/Σ_{k=1}^N λₖCₖ)[Ψ(x₀) − Ψ*
  + (L_Ψσ²/2) Σ_{k=1}^N λₖ²(1 + ((λₖ − βₖ)²/(αₖΓₖλₖ²)) Σ_{τ=k}^N Γ_τ)]`,
the expectation being over `R` and `ξ_[N]`. -/
theorem theorem_3_a {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ) (hL : 0 < LΨ)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ) (σ : ℝ)
    (α β lam : ℕ → ℝ) (hstep : RSAGStepsizes α β lam) (x0 : E n)
    (hA1 : GhadimiLan.RSG.AssumptionA1 μ ℱ g G ξ (xmdSeq G α β lam x0 ξ) σ)
    (hbdd : BddBelow (Set.range Ψ)) (N : ℕ) (hN : 1 ≤ N)
    (h27 : (∀ k ∈ Finset.Icc 1 N, 0 < NonconvexAG.Smooth.C LΨ α β lam N k))
    (R : Ω → ℕ) (hR : IsOutputIndex μ R N (pmfA LΨ α β lam N))
    (hRind : IndepFun R (fun ω k => ξ k ω) μ) :
    Integrable (fun ω => ‖g (xmdSeq G α β lam x0 ξ (R ω) ω)‖ ^ 2) μ ∧
      ∫ ω, ‖g (xmdSeq G α β lam x0 ξ (R ω) ω)‖ ^ 2 ∂μ ≤
        1 / (∑ k ∈ Finset.Icc 1 N, lam k * NonconvexAG.Smooth.C LΨ α β lam N k) *
          (Ψ x0 - (⨅ x, Ψ x) + LΨ * σ ^ 2 / 2 * ∑ k ∈ Finset.Icc 1 N,
            lam k ^ 2 * (1 + (lam k - β k) ^ 2 / (α k * NonconvexAG.Smooth.Gamma α k * lam k ^ 2) *
              ∑ τ ∈ Finset.Icc k N, NonconvexAG.Smooth.Gamma α τ)) := by sorry

end NonconvexAG.Stoch
