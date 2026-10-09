-- Prove2me | Theorems.Thm_NonconvexAG_Stoch_weighting_identity_a
-- name    : NonconvexAG.Stoch.weighting_identity_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:23:07.120307+00:00
-- url     : https://prove2.me/theorems/1c186c9c-1108-4742-8a93-5772cf3de313
-- title:
--   Weighting identity E‖∇Ψ(x^md_R)‖² = Σ λ_kC_k E‖∇Ψ(x^md_k)‖² / Σ λ_kC_k (p. 17)
-- statement:
--   Let $\Psi:\mathbb R^n\to\mathbb R$ be differentiable with $L_\Psi$-Lipschitz gradient ($L_\Psi>0$), let the oracle $G$ be jointly measurable, and run the RSAG method (Algorithm 3) from $x_0$ with step sizes $\alpha_1=1$, $\alpha_k\in(0,1)$ ($k\ge2$), $\beta_k,\lambda_k>0$, on noise $\xi_1,\xi_2,\dots$. Fix $N\ge1$, assume $C_k>0$ for $k=1,\dots,N$ (2.7), and let the termination index $R$ take values in $\{1,\dots,N\}$ with the mass function (3.4),
--   $$\Pr\{R=k\}=\frac{\lambda_kC_k}{\sum_{j=1}^N\lambda_jC_j},$$
--   independently of the noise sequence. If $\|\nabla\Psi(x^{md}_k)\|^2$ is integrable for $k=1,\dots,N$, then $\|\nabla\Psi(x^{md}_R)\|^2$ is integrable and
--   $$\mathbb E\big[\|\nabla\Psi(x^{md}_R)\|^2\big]=\frac{\sum_{k=1}^N\lambda_kC_k\,\mathbb E\|\nabla\Psi(x^{md}_k)\|^2}{\sum_{k=1}^N\lambda_kC_k},$$
--   the expectation on the left being over both $R$ and the noise.
--
--   This is the step at which the random termination enters: the expected squared gradient at the random output is the $p$-weighted average along the trajectory.
--
--   **Formalization Note** The independence of $R$ from the noise is implicit in the paper (step 0 draws $R$ before any oracle call); it is stated explicitly, and without it the identity fails. The left side is the integral of $\omega\mapsto\|\nabla\Psi(x^{md}_{R(\omega)}(\omega))\|^2$.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 17, §3.1, display before "we obtain (3.5)"

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_Stoch_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace NonconvexAG.Stoch

open GhadimiLan.RSG (E)

/-- The weighting identity of the proof of Theorem 3 a) (p. 17, display before "we obtain
(3.5)"): if `Cₖ > 0` for `k = 1, …, N` (2.7), the termination index `R` has the mass function
(3.4) on `{1, …, N}` and is independent of the noise sequence `(ξₖ)`, and each
`‖∇Ψ(x^md_k)‖²` (`k = 1, …, N`) is integrable, then `‖∇Ψ(x^md_R)‖²` is integrable and
`E‖∇Ψ(x^md_R)‖² = Σ_{k=1}^N λₖCₖ E‖∇Ψ(x^md_k)‖² / Σ_{k=1}^N λₖCₖ`, the expectation on the left
being over `R` and the noise. -/
theorem weighting_identity_a {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ) (hL : 0 < LΨ)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Ξ) (α β lam : ℕ → ℝ) (hstep : RSAGStepsizes α β lam) (x0 : E n)
    (N : ℕ) (hN : 1 ≤ N) (hC : ∀ k ∈ Finset.Icc 1 N, 0 < NonconvexAG.Smooth.C LΨ α β lam N k)
    (R : Ω → ℕ) (hR : IsOutputIndex μ R N (pmfA LΨ α β lam N))
    (hRind : IndepFun R (fun ω k => ξ k ω) μ)
    (hint : ∀ k ∈ Finset.Icc 1 N,
      Integrable (fun ω => ‖g (xmdSeq G α β lam x0 ξ k ω)‖ ^ 2) μ) :
    Integrable (fun ω => ‖g (xmdSeq G α β lam x0 ξ (R ω) ω)‖ ^ 2) μ ∧
    ∫ ω, ‖g (xmdSeq G α β lam x0 ξ (R ω) ω)‖ ^ 2 ∂μ =
      (∑ k ∈ Finset.Icc 1 N,
          lam k * NonconvexAG.Smooth.C LΨ α β lam N k * ∫ ω, ‖g (xmdSeq G α β lam x0 ξ k ω)‖ ^ 2 ∂μ) /
        ∑ k ∈ Finset.Icc 1 N, lam k * NonconvexAG.Smooth.C LΨ α β lam N k := by sorry

end NonconvexAG.Stoch
