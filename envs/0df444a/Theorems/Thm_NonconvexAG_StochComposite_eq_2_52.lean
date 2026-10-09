-- Prove2me | Theorems.Thm_NonconvexAG_StochComposite_eq_2_52
-- name    : NonconvexAG.StochComposite.eq_2_52
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:24:34.430013+00:00
-- url     : https://prove2.me/theorems/7464aea5-456a-4c61-acba-74e1d7ab51f5
-- title:
--   (2.52) — ‖x^md_k − x*‖² + α_k(1 − α_k)‖x^ag_{k−1} − x_{k−1}‖² ≤ 2(‖x*‖² + 2M²), along Algorithm 4
-- statement:
--   Suppose the prox map satisfies Assumption 2 with constant $M$ and the starting point satisfies $\|x_0\|\le M$. Run Algorithm 4 along any realization of the oracle samples. Then for every $k\ge1$ and every point $x^*\in\mathbb R^n$,
--   $$\|x^{md}_k-x^*\|^2+\alpha_k(1-\alpha_k)\|x^{ag}_{k-1}-x_{k-1}\|^2\le2\big(\|x^*\|^2+2M^2\big).$$
--
--   All iterates produced by prox steps lie in the $M$-ball, which turns the $L_f$-terms of the summed inequality into a constant.
--
--   **Formalization Note** The hypothesis $\|x_0\|\le M$ is added: at $k=1$ the bound uses $\|x^{ag}_0\|,\|x_0\|\le M$, and $x_0$ is the input, not an output of $\mathcal P$, so Assumption 2 does not cover it. It holds whenever $x_0\in\operatorname{dom}\mathcal X$. The paper applies (2.52) at an optimal solution $x^*$; it holds for every point. Restated from mission 2 of this series.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 13, (2.52)

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

/-- (2.52), p. 13 (outer ends of the chain), along Algorithm 4: under Assumption 2 and
`‖x₀‖ ≤ M`, for every realization `ω`, every `k ≥ 1` and every point `x*` (the paper applies
it at an optimal solution). -/
theorem eq_2_52 {n : ℕ} (P : E n → E n → ℝ → E n) (M : ℝ) (hA2 : Assumption2 P M)
    {Ξ : Type*} (G : E n → Ξ → E n)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (hstep : RSAGStepsizes α β lam m) (x0 : E n)
    (hx0 : ‖x0‖ ≤ M) {Ω : Type*} (ξ : ℕ → Ω → Ξ) :
    let xk : ℕ → Ω → E n := xSeq G P α β lam m x0 ξ
    let xag : ℕ → Ω → E n := xagSeq G P α β lam m x0 ξ
    let xmd : ℕ → Ω → E n := xmdSeq G P α β lam m x0 ξ
    ∀ ω : Ω, ∀ k, 1 ≤ k → ∀ xstar : E n,
      ‖xmd k ω - xstar‖ ^ 2 + α k * (1 - α k) * ‖xag (k - 1) ω - xk (k - 1) ω‖ ^ 2 ≤
        2 * (‖xstar‖ ^ 2 + 2 * M ^ 2) := by sorry

end NonconvexAG.StochComposite
