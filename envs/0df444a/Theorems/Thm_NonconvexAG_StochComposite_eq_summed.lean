-- Prove2me | Theorems.Thm_NonconvexAG_StochComposite_eq_summed
-- name    : NonconvexAG.StochComposite.eq_summed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:24:11.284233+00:00
-- url     : https://prove2.me/theorems/54c6736f-ce0c-4dfb-b5cc-b2769c085e91
-- title:
--   §3.2, last display of p. 22 — the one-step inequality summed over k = 1, …, N
-- statement:
--   In the setting of the one-step inequality after (3.34), fix $N\ge1$ and assume, for $k=1,\dots,N$, (2.9): $\alpha_k\lambda_k\le\beta_k<1/L_\Psi$, and (2.10): $\frac{\alpha_1}{\lambda_1\Gamma_1}\ge\frac{\alpha_2}{\lambda_2\Gamma_2}\ge\cdots\ge\frac{\alpha_N}{\lambda_N\Gamma_N}$. Then along every realization of the oracle samples and for every $x\in K$,
--   $$\begin{aligned}\frac{\Phi(x^{ag}_N)-\Phi(x)}{\Gamma_N}+\sum_{k=1}^N\frac{1-L_\Psi\beta_k}{4\beta_k\Gamma_k}\|x^{ag}_k-x^{md}_k\|^2\le{}&\frac{\|x_0-x\|^2}{2\lambda_1}+\sum_{k=1}^N\frac{\alpha_k}{\Gamma_k}\langle\bar\delta_k,x-x_{k-1}\rangle\\&+\frac{L_f}2\sum_{k=1}^N\frac{\alpha_k}{\Gamma_k}\Big[\|x^{md}_k-x\|^2+\alpha_k(1-\alpha_k)\|x^{ag}_{k-1}-x_{k-1}\|^2\Big]+\sum_{k=1}^N\frac{\beta_k\|\bar\delta_k\|^2}{\Gamma_k(1-L_\Psi\beta_k)} .\end{aligned}$$
--
--   **Formalization Note** Pathwise, for $x\in K$ (the paper's "for all $x\in\mathbb R^n$"; off $K$ the left side is $-\infty$). (2.9) and (2.10) are imposed on $\{1,\dots,N\}$ only, (2.10) as $\alpha_k/(\lambda_k\Gamma_k)\le\alpha_{k-1}/(\lambda_{k-1}\Gamma_{k-1})$ for $2\le k\le N$.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 22, §3.2, last display of the page

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

/-- §3.2, last display of p. 22: the summed inequality along Algorithm 4, for every realization
`ω`, every `N ≥ 1` and every `x` in the domain `K` of `𝒳`, when (2.9)
(`αₖλₖ ≤ βₖ`, `L_Ψ βₖ < 1`) and (2.10) hold for `k = 1, …, N`. -/
theorem eq_summed {n : ℕ} (f h : E n → ℝ) (gf gh : E n → E n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h)
    (Ψ : E n → ℝ) (gΨ : E n → E n) (LΨ : ℝ) (hΨ : Ψ = fun x => f x + h x)
    (hgΨ : gΨ = fun x => gf x + gh x) (hLΨ : LΨ = Lf + Lh)
    (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P) {Ξ : Type*} (G : E n → Ξ → E n)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (hstep : RSAGStepsizes α β lam m) (x0 : E n)
    {Ω : Type*} (ξ : ℕ → Ω → Ξ)
    (N : ℕ) (hN : 1 ≤ N) (h29 : ∀ k ∈ Finset.Icc 1 N, α k * lam k ≤ β k ∧ LΨ * β k < 1)
    (h210 : ∀ k ∈ Finset.Icc 1 N, 2 ≤ k →
      α k / (lam k * NonconvexAG.Smooth.Gamma α k) ≤ α (k - 1) / (lam (k - 1) * NonconvexAG.Smooth.Gamma α (k - 1))) :
    let Φ : E n → ℝ := fun x => Ψ x + X x
    let xk : ℕ → Ω → E n := xSeq G P α β lam m x0 ξ
    let xag : ℕ → Ω → E n := xagSeq G P α β lam m x0 ξ
    let xmd : ℕ → Ω → E n := xmdSeq G P α β lam m x0 ξ
    let δ : ℕ → Ω → E n := deltaBar G gΨ P α β lam m x0 ξ
    ∀ ω : Ω, ∀ x ∈ K,
      (Φ (xag N ω) - Φ x) / NonconvexAG.Smooth.Gamma α N +
          ∑ k ∈ Finset.Icc 1 N,
            (1 - LΨ * β k) / (4 * β k * NonconvexAG.Smooth.Gamma α k) * ‖xag k ω - xmd k ω‖ ^ 2 ≤
        ‖x0 - x‖ ^ 2 / (2 * lam 1) +
          ∑ k ∈ Finset.Icc 1 N, α k / NonconvexAG.Smooth.Gamma α k * inner ℝ (δ k ω) (x - xk (k - 1) ω) +
          Lf / 2 * ∑ k ∈ Finset.Icc 1 N, α k / NonconvexAG.Smooth.Gamma α k *
            (‖xmd k ω - x‖ ^ 2 + α k * (1 - α k) * ‖xag (k - 1) ω - xk (k - 1) ω‖ ^ 2) +
          ∑ k ∈ Finset.Icc 1 N, β k * ‖δ k ω‖ ^ 2 / (NonconvexAG.Smooth.Gamma α k * (1 - LΨ * β k)) := by sorry

end NonconvexAG.StochComposite
