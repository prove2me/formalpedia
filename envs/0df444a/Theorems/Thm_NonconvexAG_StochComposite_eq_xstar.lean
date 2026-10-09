-- Prove2me | Theorems.Thm_NonconvexAG_StochComposite_eq_xstar
-- name    : NonconvexAG.StochComposite.eq_xstar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:24:18.795219+00:00
-- url     : https://prove2.me/theorems/1ed948eb-ab86-441d-b533-a856b608db30
-- title:
--   §3.2, first display of p. 23 — the summed inequality at x = x*
-- statement:
--   In the setting of the summed inequality (last display of p. 22), assume also Assumption 2 with constant $M$ and $\|x_0\|\le M$. Then along every realization of the oracle samples and for every $x^*\in K$,
--   $$\frac{\Phi(x^{ag}_N)-\Phi(x^*)}{\Gamma_N}+\sum_{k=1}^N\frac{1-L_\Psi\beta_k}{4\beta_k\Gamma_k}\|x^{ag}_k-x^{md}_k\|^2\le\frac{\|x_0-x^*\|^2}{2\lambda_1}+\sum_{k=1}^N\frac{\alpha_k}{\Gamma_k}\langle\bar\delta_k,x^*-x_{k-1}\rangle+\frac{L_f}{\Gamma_N}\big(\|x^*\|^2+2M^2\big)+\sum_{k=1}^N\frac{\beta_k\|\bar\delta_k\|^2}{\Gamma_k(1-L_\Psi\beta_k)} .$$
--
--   **Formalization Note** Pathwise. The paper sets $x=x^*$, an optimal solution; only $x^*\in K$ is used, so that is the hypothesis. $\|x_0\|\le M$ is added as in (2.52).
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 23, §3.2, first display of the page

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

/-- §3.2, first display of p. 23: the summed inequality at `x = x*`, with the `L_f`-terms bounded
by (2.16) and (2.52), along Algorithm 4, for every realization `ω`, every `N ≥ 1` and every
point `x*` of the domain `K` of `𝒳`, under Assumption 2, `‖x₀‖ ≤ M`, and (2.9), (2.10) for
`k = 1, …, N`. -/
theorem eq_xstar {n : ℕ} (f h : E n → ℝ) (gf gh : E n → E n) (Lf Lh : ℝ)
    (hf : IsBetaSmooth f gf Lf) (hh : IsBetaSmooth h gh Lh) (hhc : ConvexOn ℝ Set.univ h)
    (Ψ : E n → ℝ) (gΨ : E n → E n) (LΨ : ℝ) (hΨ : Ψ = fun x => f x + h x)
    (hgΨ : gΨ = fun x => gf x + gh x) (hLΨ : LΨ = Lf + Lh)
    (K : Set (E n)) (X : E n → ℝ) (hX : ConvexOn ℝ K X)
    (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P) {Ξ : Type*} (G : E n → Ξ → E n)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (hstep : RSAGStepsizes α β lam m) (x0 : E n)
    (M : ℝ) (hA2 : Assumption2 P M) (hx0 : ‖x0‖ ≤ M)
    {Ω : Type*} (ξ : ℕ → Ω → Ξ)
    (N : ℕ) (hN : 1 ≤ N) (h29 : ∀ k ∈ Finset.Icc 1 N, α k * lam k ≤ β k ∧ LΨ * β k < 1)
    (h210 : ∀ k ∈ Finset.Icc 1 N, 2 ≤ k →
      α k / (lam k * NonconvexAG.Smooth.Gamma α k) ≤ α (k - 1) / (lam (k - 1) * NonconvexAG.Smooth.Gamma α (k - 1))) :
    let Φ : E n → ℝ := fun x => Ψ x + X x
    let xk : ℕ → Ω → E n := xSeq G P α β lam m x0 ξ
    let xag : ℕ → Ω → E n := xagSeq G P α β lam m x0 ξ
    let xmd : ℕ → Ω → E n := xmdSeq G P α β lam m x0 ξ
    let δ : ℕ → Ω → E n := deltaBar G gΨ P α β lam m x0 ξ
    ∀ ω : Ω, ∀ xstar ∈ K,
      (Φ (xag N ω) - Φ xstar) / NonconvexAG.Smooth.Gamma α N +
          ∑ k ∈ Finset.Icc 1 N,
            (1 - LΨ * β k) / (4 * β k * NonconvexAG.Smooth.Gamma α k) * ‖xag k ω - xmd k ω‖ ^ 2 ≤
        ‖x0 - xstar‖ ^ 2 / (2 * lam 1) +
          ∑ k ∈ Finset.Icc 1 N, α k / NonconvexAG.Smooth.Gamma α k * inner ℝ (δ k ω) (xstar - xk (k - 1) ω) +
          Lf / NonconvexAG.Smooth.Gamma α N * (‖xstar‖ ^ 2 + 2 * M ^ 2) +
          ∑ k ∈ Finset.Icc 1 N, β k * ‖δ k ω‖ ^ 2 / (NonconvexAG.Smooth.Gamma α k * (1 - LΨ * β k)) := by sorry

end NonconvexAG.StochComposite
