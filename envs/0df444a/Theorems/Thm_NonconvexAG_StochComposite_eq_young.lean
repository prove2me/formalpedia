-- Prove2me | Theorems.Thm_NonconvexAG_StochComposite_eq_young
-- name    : NonconvexAG.StochComposite.eq_young
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:23:56.926607+00:00
-- url     : https://prove2.me/theorems/4fb62e28-9176-4355-b5b2-dfa223b8f8fc
-- title:
--   §3.2, display after (3.34), p. 22 — the one-step inequality for Φ = Ψ + 𝒳 with the noise term δ̄_k
-- statement:
--   Let $\Psi=f+h$ be as in Lemma 5, $\mathcal X$ convex with domain $K$ and prox map $\mathcal P$, $\Phi=\Psi+\mathcal X$, and run Algorithm 4 along any realization of the oracle samples. For every $k\ge1$ with $\alpha_k\lambda_k\le\beta_k$ and $L_\Psi\beta_k<1$, and every $x\in K$,
--   $$\begin{aligned}\Phi(x^{ag}_k)\le{}&(1-\alpha_k)\Phi(x^{ag}_{k-1})+\alpha_k\Phi(x)+\langle\bar\delta_k,\alpha_k(x-x_{k-1})\rangle-\frac14\Big(\frac1{\beta_k}-L_\Psi\Big)\|x^{ag}_k-x^{md}_k\|^2+\frac{\beta_k\|\bar\delta_k\|^2}{1-L_\Psi\beta_k}\\&+\frac{\alpha_k}{2\lambda_k}\Big[\|x_{k-1}-x\|^2-\|x_k-x\|^2\Big]+\frac{L_f\alpha_k}2\|x^{md}_k-x\|^2+\frac{L_f\alpha_k^2(1-\alpha_k)}2\|x^{ag}_{k-1}-x_{k-1}\|^2 .\end{aligned}$$
--
--   It is the stochastic counterpart of (2.51): the noise $\bar\delta_k$ contributes a linear term, which vanishes in expectation, and a quadratic term.
--
--   **Formalization Note** Pathwise; this is the last line of the printed chain. $\beta_k<1/L_\Psi$ of (2.9) is written $L_\Psi\beta_k<1$, which needs no sign condition on $L_\Psi$.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 22, §3.2, display after (3.34)

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

/-- §3.2, display after (3.34), p. 22 (outer ends of the chain): the one-step inequality for
`Φ = Ψ + 𝒳` along Algorithm 4, for every realization `ω`, every `k ≥ 1` with (2.9)
(`αₖλₖ ≤ βₖ` and `L_Ψ βₖ < 1`) and every `x` in the domain `K` of `𝒳`. -/
theorem eq_young {n : ℕ} (f h : E n → ℝ) (gf gh : E n → E n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h)
    (Ψ : E n → ℝ) (gΨ : E n → E n) (LΨ : ℝ) (hΨ : Ψ = fun x => f x + h x)
    (hgΨ : gΨ = fun x => gf x + gh x) (hLΨ : LΨ = Lf + Lh)
    (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P) {Ξ : Type*} (G : E n → Ξ → E n)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (hstep : RSAGStepsizes α β lam m) (x0 : E n)
    {Ω : Type*} (ξ : ℕ → Ω → Ξ) :
    let Φ : E n → ℝ := fun x => Ψ x + X x
    let xk : ℕ → Ω → E n := xSeq G P α β lam m x0 ξ
    let xag : ℕ → Ω → E n := xagSeq G P α β lam m x0 ξ
    let xmd : ℕ → Ω → E n := xmdSeq G P α β lam m x0 ξ
    let δ : ℕ → Ω → E n := deltaBar G gΨ P α β lam m x0 ξ
    ∀ ω : Ω, ∀ k, 1 ≤ k → α k * lam k ≤ β k → LΨ * β k < 1 → ∀ x ∈ K,
      Φ (xag k ω) ≤ (1 - α k) * Φ (xag (k - 1) ω) + α k * Φ x +
          inner ℝ (δ k ω) (α k • (x - xk (k - 1) ω)) -
          1 / 4 * (1 / β k - LΨ) * ‖xag k ω - xmd k ω‖ ^ 2 +
          β k * ‖δ k ω‖ ^ 2 / (1 - LΨ * β k) +
          α k / (2 * lam k) * (‖xk (k - 1) ω - x‖ ^ 2 - ‖xk k ω - x‖ ^ 2) +
          Lf * α k / 2 * ‖xmd k ω - x‖ ^ 2 +
          Lf * α k ^ 2 * (1 - α k) / 2 * ‖xag (k - 1) ω - xk (k - 1) ω‖ ^ 2 := by sorry

end NonconvexAG.StochComposite
