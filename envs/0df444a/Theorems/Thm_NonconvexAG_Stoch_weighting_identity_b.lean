-- Prove2me | Theorems.Thm_NonconvexAG_Stoch_weighting_identity_b
-- name    : NonconvexAG.Stoch.weighting_identity_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:23:14.444376+00:00
-- url     : https://prove2.me/theorems/ad9dd55d-b8ca-46ea-a423-364eeca3b207
-- title:
--   Weighting identity E[Ψ(x^ag_R) − Ψ(x)] = Σ p_k E[Ψ(x^ag_k) − Ψ(x)] for the mass function (3.7) (p. 18)
-- statement:
--   Let $\Psi:\mathbb R^n\to\mathbb R$ be differentiable with $L_\Psi$-Lipschitz gradient ($L_\Psi>0$), let the oracle $G$ be jointly measurable, and run the RSAG method (Algorithm 3) from $x_0$ with step sizes $\alpha_1=1$, $\alpha_k\in(0,1)$ ($k\ge2$), $\beta_k,\lambda_k>0$, on noise $\xi_1,\xi_2,\dots$. Fix $N\ge1$ with $\beta_k<1/L_\Psi$ for $k=1,\dots,N$, and let the termination index $R$ take values in $\{1,\dots,N\}$ with the mass function (3.7),
--   $$p_k=\Pr\{R=k\}=\frac{\Gamma_k^{-1}\beta_k(1-L_\Psi\beta_k)}{\sum_{j=1}^N\Gamma_j^{-1}\beta_j(1-L_\Psi\beta_j)},$$
--   independently of the noise sequence. If $\Psi(x^{ag}_k)$ is integrable for $k=1,\dots,N$, then for every $x\in\mathbb R^n$ (in the paper, $x=x^*$) $\Psi(x^{ag}_R)-\Psi(x)$ is integrable and
--   $$\mathbb E\big[\Psi(x^{ag}_R)-\Psi(x)\big]=\sum_{k=1}^Np_k\,\mathbb E\big[\Psi(x^{ag}_k)-\Psi(x)\big].$$
--
--   It turns the bounds at fixed horizons into the bound (3.9) at the random output.
--
--   **Formalization Note** The independence of $R$ from the noise is explicit. The identity holds for every fixed $x$; the paper uses it at $x=x^*$, and no optimality of $x$ is assumed.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 18, §3.1, first line of the last display of the proof of Theorem 3

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_Stoch_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace NonconvexAG.Stoch

open GhadimiLan.RSG (E)

/-- The weighting identity of the proof of Theorem 3 b) (p. 18, first line of the last display):
if `0 < βₖ < 1/L_Ψ` for `k = 1, …, N` (so that (3.7) is a probability mass function), the
termination index `R` has the mass function (3.7) on `{1, …, N}` and is independent of the
noise sequence `(ξₖ)`, and each `Ψ(x^ag_k)` (`k = 1, …, N`) is integrable, then for every
`x ∈ ℝⁿ` (in the paper, `x = x*`) `Ψ(x^ag_R) − Ψ(x)` is integrable and
`E[Ψ(x^ag_R) − Ψ(x)] = Σ_{k=1}^N pₖ E[Ψ(x^ag_k) − Ψ(x)]` with `pₖ` the mass function (3.7). -/
theorem weighting_identity_b {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ) (hL : 0 < LΨ)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Ξ) (α β lam : ℕ → ℝ) (hstep : RSAGStepsizes α β lam) (x0 : E n)
    (N : ℕ) (hN : 1 ≤ N) (hβ : ∀ k ∈ Finset.Icc 1 N, β k < 1 / LΨ)
    (R : Ω → ℕ) (hR : IsOutputIndex μ R N (pmfB LΨ α β N))
    (hRind : IndepFun R (fun ω k => ξ k ω) μ)
    (hint : ∀ k ∈ Finset.Icc 1 N, Integrable (fun ω => Ψ (xagSeq G α β lam x0 ξ k ω)) μ)
    (x : E n) :
    Integrable (fun ω => Ψ (xagSeq G α β lam x0 ξ (R ω) ω) - Ψ x) μ ∧
    ∫ ω, (Ψ (xagSeq G α β lam x0 ξ (R ω) ω) - Ψ x) ∂μ =
      ∑ k ∈ Finset.Icc 1 N,
        pmfB LΨ α β N k * ∫ ω, (Ψ (xagSeq G α β lam x0 ξ k ω) - Ψ x) ∂μ := by sorry

end NonconvexAG.Stoch
