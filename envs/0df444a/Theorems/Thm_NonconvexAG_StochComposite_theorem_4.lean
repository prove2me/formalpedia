-- Prove2me | Theorems.Thm_NonconvexAG_StochComposite_theorem_4
-- name    : NonconvexAG.StochComposite.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:24:55.785721+00:00
-- url     : https://prove2.me/theorems/183c6b4d-2d38-4b6c-ae48-66472dc123a6
-- title:
--   Theorem 4 — the mini-batch RSAG method bounds E‖𝒢(x^md_R, ∇Ψ(x^md_R), β_R)‖² on nonconvex stochastic composite problems
-- statement:
--   Consider the stochastic composite problem
--   $$\min_{x\in\mathbb R^n}\ \Phi(x):=\Psi(x)+\mathcal X(x),\qquad\Psi=f+h,$$
--   where $f$ is differentiable with $L_f$-Lipschitz gradient (possibly nonconvex), $h$ is convex and differentiable with $L_h$-Lipschitz gradient, $L_\Psi=L_f+L_h$, and $\mathcal X$ is convex with domain $K$; let $x^*\in K$ be an optimal solution. Let the prox map $\mathcal P$ (2.37) satisfy Assumption 2 with constant $M$, and let $\|x_0\|\le M$. The stochastic oracle $G$ is jointly measurable and satisfies Assumption 1 with noise level $\sigma$ along its query points, in conditional form.
--
--   Run Algorithm 4 (mini-batch gradients $\bar G_k$ of sizes $m_k\ge1$) for $N\ge1$ iterations with step sizes satisfying, for $k=1,\dots,N$,
--   $$\alpha_k\lambda_k\le\beta_k<\frac1{L_\Psi}\ \ (2.9),\qquad\frac{\alpha_1}{\lambda_1\Gamma_1}\ge\frac{\alpha_2}{\lambda_2\Gamma_2}\ge\cdots\ \ (2.10),$$
--   and let the output index $R$, independent of the oracle samples, have the mass function (3.7), $p_k=\Gamma_k^{-1}\beta_k(1-L_\Psi\beta_k)/S$ with $S=\sum_{k=1}^N\Gamma_k^{-1}\beta_k(1-L_\Psi\beta_k)$. Then
--   $$\mathbb E\Big[\big\|\mathcal G(x^{md}_R,\nabla\Psi(x^{md}_R),\beta_R)\big\|^2\Big]\le8S^{-1}\Big[\frac{\|x_0-x^*\|^2}{2\lambda_1}+\frac{L_f}{\Gamma_N}\big(\|x^*\|^2+2M^2\big)+\sigma^2\sum_{k=1}^N\frac{\beta_k\big(4+(1-L_\Psi\beta_k)^2\big)}{4\Gamma_k(1-L_\Psi\beta_k)m_k}\Big],\qquad(3.30)$$
--   the expectation being over $R$ and all samples $\xi_{k,i}$, $k\le N$, $i\le m_k$. If, in addition, $L_f=0$, then
--   $$\mathbb E\big[\Phi(x^{ag}_R)-\Phi(x^*)\big]\le S^{-1}\sum_{k=1}^N\beta_k(1-L_\Psi\beta_k)\Big(\frac{\|x_0-x^*\|^2}{2\lambda_1}+\sigma^2\sum_{j=1}^k\frac{\beta_j\big(4+(1-L_\Psi\beta_j)^2\big)}{4\Gamma_j(1-L_\Psi\beta_j)m_j}\Big).\qquad(3.31)$$
--   Both random quantities are integrable.
--
--   The same step-size policy thus gives a stationarity guarantee when $\Psi$ is nonconvex and an optimality-gap guarantee when $L_f=0$ (convex $\Psi$), with the oracle noise controlled by the batch sizes $m_k$. Corollaries 4 and 5 specialize it to explicit step sizes and batch sizes.
--
--   **Formalization Note** Hypotheses added to the printed statement: existence of an optimal solution $x^*$ (the statement uses it; Corollaries 4–5 assume it) and $\|x_0\|\le M$ (needed for (2.52) at $k=1$). $\beta_k<1/L_\Psi$ is written $L_\Psi\beta_k<1$. Assumption 1 is the published `GhadimiLan.RSG.AssumptionA1`, imposed on the oracle calls numbered consecutively, with each call's query point $x^{md}_k$ of its iteration; this conditional form is what the variance bound (3.28) and the martingale step of the proof use, and it holds in the i.i.d. setting. $R$ is measurable with values in $\{1,\dots,N\}$ and independent of the whole sample sequence. $\mathcal X$ is the pair (domain $K$, real values on $K$), and $x^*$ is optimal over $K$. Integrability is part of the conclusion.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, pp. 21–22, Theorem 4, (3.30)–(3.31); p. 5, (2.9)–(2.10); p. 15, (3.7)

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

/-- Theorem 4 (pp. 21–22): (3.30), and (3.31) when `L_f = 0`. The problem is (1.3):
`Ψ = f + h` with `f ∈ C^{1,1}_{L_f}`, `h ∈ C^{1,1}_{L_h}` convex, `L_Ψ = L_f + L_h`, and `𝒳` convex
with domain `K`; `Φ = Ψ + 𝒳`, with an optimal solution `x*`. Algorithm 4 runs with the prox map
`P` of (2.37) and mini-batches of sizes `mₖ ≥ 1`, under Assumption 1 (conditional form, along the
oracle's query points) and Assumption 2, with `‖x₀‖ ≤ M`, (2.9) (`αₖλₖ ≤ βₖ` and `L_Ψ βₖ < 1`, i.e.
`βₖ < 1/L_Ψ`) and (2.10) for `k = 1, …, N`, and a termination index `R` with mass function (3.7)
on `{1, …, N}`, independent of the oracle noise. The expectations are over `R` and the noise. -/
theorem theorem_4 {n : ℕ} (f h : E n → ℝ) (gf gh : E n → E n) (Lf Lh : ℝ)
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
    (xstar : E n) (hxstar : xstar ∈ K) (hopt : ∀ u ∈ K, Ψ xstar + X xstar ≤ Ψ u + X u)
    (R : Ω → ℕ) (hR : NonconvexAG.Stoch.IsOutputIndex μ R N (pmf37 LΨ α β N))
    (hRind : IndepFun R (fun ω s => ξ s ω) μ) :
    let Φ : E n → ℝ := fun x => Ψ x + X x
    let xag : ℕ → Ω → E n := xagSeq G P α β lam m x0 ξ
    let xmd : ℕ → Ω → E n := xmdSeq G P α β lam m x0 ξ
    let S : ℝ := ∑ k ∈ Finset.Icc 1 N, (NonconvexAG.Smooth.Gamma α k)⁻¹ * β k * (1 - LΨ * β k)
    let v : ℕ → ℝ := fun j =>
      β j * (4 + (1 - LΨ * β j) ^ 2) / (4 * NonconvexAG.Smooth.Gamma α j * (1 - LΨ * β j) * (m j : ℝ))
    -- (3.30)
    (Integrable (fun ω =>
        ‖gradMap P (xmd (R ω) ω) (gΨ (xmd (R ω) ω)) (β (R ω))‖ ^ 2) μ ∧
      ∫ ω, ‖gradMap P (xmd (R ω) ω) (gΨ (xmd (R ω) ω)) (β (R ω))‖ ^ 2 ∂μ ≤
        8 * S⁻¹ * (‖x0 - xstar‖ ^ 2 / (2 * lam 1) + Lf / NonconvexAG.Smooth.Gamma α N * (‖xstar‖ ^ 2 + 2 * M ^ 2) +
          σ ^ 2 * ∑ k ∈ Finset.Icc 1 N, v k)) ∧
    -- (3.31)
    (Lf = 0 →
      Integrable (fun ω => Φ (xag (R ω) ω) - Φ xstar) μ ∧
        ∫ ω, (Φ (xag (R ω) ω) - Φ xstar) ∂μ ≤
          S⁻¹ * ∑ k ∈ Finset.Icc 1 N, β k * (1 - LΨ * β k) *
            (‖x0 - xstar‖ ^ 2 / (2 * lam 1) + σ ^ 2 * ∑ j ∈ Finset.Icc 1 k, v j)) := by sorry

end NonconvexAG.StochComposite
