-- Prove2me | Theorems.Thm_NonconvexAG_StochComposite_eq_3_35
-- name    : NonconvexAG.StochComposite.eq_3_35
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:23:51.074841+00:00
-- url     : https://prove2.me/theorems/6fb58dde-0103-47d4-b8c9-e46e387d5605
-- title:
--   (3.35) — the expected gap and the expected gradient mappings of Algorithm 4 over N iterations
-- statement:
--   Consider the stochastic composite problem ($\Psi=f+h$ as in Lemma 5, $\mathcal X$ convex with domain $K$, $\Phi=\Psi+\mathcal X$) under Assumption 2 with constant $M$, $\|x_0\|\le M$, and Assumption 1 in conditional form along the oracle's query points, with a jointly measurable oracle. Run Algorithm 4 with batch sizes $m_k\ge1$, fix $N\ge1$, and assume (2.9) and (2.10) for $k=1,\dots,N$. Then for every $x^*\in K$ the quantities $\Phi(x^{ag}_N)-\Phi(x^*)$ and $\|\mathcal G(x^{md}_k,\nabla\Psi(x^{md}_k),\beta_k)\|^2$ ($k=1,\dots,N$) are integrable and
--   $$\frac{\mathbb E\big[\Phi(x^{ag}_N)-\Phi(x^*)\big]}{\Gamma_N}+\sum_{k=1}^N\frac{\beta_k(1-L_\Psi\beta_k)}{8\Gamma_k}\mathbb E\Big[\big\|\mathcal G(x^{md}_k,\nabla\Psi(x^{md}_k),\beta_k)\big\|^2\Big]\le\frac{\|x_0-x^*\|^2}{2\lambda_1}+\frac{L_f}{\Gamma_N}\big(\|x^*\|^2+2M^2\big)+\sigma^2\sum_{k=1}^N\frac{\beta_k\big(4+(1-L_\Psi\beta_k)^2\big)}{4\Gamma_k(1-L_\Psi\beta_k)m_k},$$
--   the expectations being over all oracle samples $\xi_{k,i}$, $k\le N$, $i\le m_k$.
--
--   This is the stochastic analogue of (2.53); Theorem 4 follows from it by averaging over the random output index.
--
--   **Formalization Note** The page prints $\Phi(x)$ on the left of (3.35); after the substitution $x=x^*$ it means $\Phi(x^*)$, which is stated. The final form of the printed chain is stated. Only $x^*\in K$ is assumed (not its optimality). Integrability is part of the conclusion.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 23, (3.35)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_StochComposite_ProxMap
import Definitions.Def_NonconvexAG_StochComposite_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace NonconvexAG.StochComposite

open GhadimiLan.RSG (E)
open ConvexOptAlg.SmoothGD

/-- (3.35), p. 23 (outer ends of the chain, with `Φ(x*)` for the printed `Φ(x)` on the left), for
Algorithm 4: under Assumptions 1 (conditional form, along the query points) and 2, `‖x₀‖ ≤ M`,
and (2.9), (2.10) for `k = 1, …, N` (`N ≥ 1`), for every point `x*` of the domain `K` of `𝒳`
the quantities `Φ(x^ag_N) − Φ(x*)` and `‖𝒢(x^md_k, ∇Ψ(x^md_k), βₖ)‖²` (`k = 1, …, N`) are
integrable and
`E[Φ(x^ag_N) − Φ(x*)]/Γ_N + Σ_{k=1}^N (βₖ(1 − L_Ψβₖ)/(8Γₖ)) E‖𝒢(x^md_k, ∇Ψ(x^md_k), βₖ)‖²
  ≤ ‖x₀ − x*‖²/(2λ₁) + (L_f/Γ_N)(‖x*‖² + 2M²) + σ² Σ_{k=1}^N βₖ(4 + (1 − L_Ψβₖ)²)/(4Γₖ(1 − L_Ψβₖ)mₖ)`. -/
theorem eq_3_35 {n : ℕ} (f h : E n → ℝ) (gf gh : E n → E n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h)
    (Ψ : E n → ℝ) (gΨ : E n → E n) (LΨ : ℝ) (hΨ : Ψ = fun x => f x + h x)
    (hgΨ : gΨ = fun x => gf x + gh x) (hLΨ : LΨ = Lf + Lh)
    (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ) (σ : ℝ)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (hstep : RSAGStepsizes α β lam m) (x0 : E n)
    (hA1 : GhadimiLan.RSG.AssumptionA1 μ ℱ gΨ G ξ (querySeq G P α β lam m x0 ξ) σ)
    (M : ℝ) (hA2 : Assumption2 P M) (hx0 : ‖x0‖ ≤ M)
    (N : ℕ) (hN : 1 ≤ N) (h29 : ∀ k ∈ Finset.Icc 1 N, α k * lam k ≤ β k ∧ LΨ * β k < 1)
    (h210 : ∀ k ∈ Finset.Icc 1 N, 2 ≤ k →
      α k / (lam k * NonconvexAG.Smooth.Gamma α k) ≤ α (k - 1) / (lam (k - 1) * NonconvexAG.Smooth.Gamma α (k - 1)))
    (xstar : E n) (hxstar : xstar ∈ K) :
    let Φ : E n → ℝ := fun x => Ψ x + X x
    let xag : ℕ → Ω → E n := xagSeq G P α β lam m x0 ξ
    let xmd : ℕ → Ω → E n := xmdSeq G P α β lam m x0 ξ
    Integrable (fun ω => Φ (xag N ω) - Φ xstar) μ ∧
    (∀ k ∈ Finset.Icc 1 N,
      Integrable (fun ω => ‖gradMap P (xmd k ω) (gΨ (xmd k ω)) (β k)‖ ^ 2) μ) ∧
    (∫ ω, (Φ (xag N ω) - Φ xstar) ∂μ) / NonconvexAG.Smooth.Gamma α N +
        ∑ k ∈ Finset.Icc 1 N, β k * (1 - LΨ * β k) / (8 * NonconvexAG.Smooth.Gamma α k) *
          ∫ ω, ‖gradMap P (xmd k ω) (gΨ (xmd k ω)) (β k)‖ ^ 2 ∂μ ≤
      ‖x0 - xstar‖ ^ 2 / (2 * lam 1) + Lf / NonconvexAG.Smooth.Gamma α N * (‖xstar‖ ^ 2 + 2 * M ^ 2) +
        σ ^ 2 * ∑ k ∈ Finset.Icc 1 N,
          β k * (4 + (1 - LΨ * β k) ^ 2) / (4 * NonconvexAG.Smooth.Gamma α k * (1 - LΨ * β k) * (m k : ℝ)) := by sorry

end NonconvexAG.StochComposite
