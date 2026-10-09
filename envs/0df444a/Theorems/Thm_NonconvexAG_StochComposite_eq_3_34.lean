-- Prove2me | Theorems.Thm_NonconvexAG_StochComposite_eq_3_34
-- name    : NonconvexAG.StochComposite.eq_3_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:23:51.323481+00:00
-- url     : https://prove2.me/theorems/9dac9d2d-fa55-4ac1-83df-f507beb52efc
-- title:
--   (3.34) — the combined stochastic prox inequality under α_kλ_k ≤ β_k
-- statement:
--   In the setting of (3.32)–(3.33), for every $k\ge1$ with $\alpha_k\lambda_k\le\beta_k$ and every $x\in K$,
--   $$\langle\nabla\Psi(x^{md}_k)+\bar\delta_k,x^{ag}_k-\alpha_kx-(1-\alpha_k)x^{ag}_{k-1}\rangle+\mathcal X(x^{ag}_k)\le(1-\alpha_k)\mathcal X(x^{ag}_{k-1})+\alpha_k\mathcal X(x)+\frac{\alpha_k}{2\lambda_k}\Big[\|x_{k-1}-x\|^2-\|x_k-x\|^2\Big]-\frac1{2\beta_k}\|x^{ag}_k-x^{md}_k\|^2 .$$
--
--   It combines the two three-point inequalities through the convexity of $\mathcal X$ and the definition (2.2) of $x^{md}_k$.
--
--   **Formalization Note** Pathwise, for $x\in K$. At $k=1$ the term $\mathcal X(x^{ag}_0)=\mathcal X(x_0)$ carries the factor $1-\alpha_1=0$, so $x_0\in K$ is not needed (the Lean `X` is a real-valued function on all of $\mathbb R^n$ whose values off $K$ are irrelevant).
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 22, (3.34)

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

/-- (3.34), p. 22 (outer ends of the chain), along Algorithm 4, for every realization `ω`, every
`k ≥ 1` with `αₖλₖ ≤ βₖ` and every `x` in the domain `K` of `𝒳`. -/
theorem eq_3_34 {n : ℕ} (gΨ : E n → E n) (K : Set (E n)) (X : E n → ℝ)
    (hX : ConvexOn ℝ K X) (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P)
    {Ξ : Type*} (G : E n → Ξ → E n)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (hstep : RSAGStepsizes α β lam m) (x0 : E n)
    {Ω : Type*} (ξ : ℕ → Ω → Ξ) :
    let xk : ℕ → Ω → E n := xSeq G P α β lam m x0 ξ
    let xag : ℕ → Ω → E n := xagSeq G P α β lam m x0 ξ
    let xmd : ℕ → Ω → E n := xmdSeq G P α β lam m x0 ξ
    let δ : ℕ → Ω → E n := deltaBar G gΨ P α β lam m x0 ξ
    ∀ ω : Ω, ∀ k, 1 ≤ k → α k * lam k ≤ β k → ∀ x ∈ K,
      inner ℝ (gΨ (xmd k ω) + δ k ω) (xag k ω - α k • x - (1 - α k) • xag (k - 1) ω) +
          X (xag k ω) ≤
        (1 - α k) * X (xag (k - 1) ω) + α k * X x +
          α k / (2 * lam k) * (‖xk (k - 1) ω - x‖ ^ 2 - ‖xk k ω - x‖ ^ 2) -
          1 / (2 * β k) * ‖xag k ω - xmd k ω‖ ^ 2 := by sorry

end NonconvexAG.StochComposite
