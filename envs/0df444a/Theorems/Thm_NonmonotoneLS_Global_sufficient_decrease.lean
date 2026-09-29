-- Prove2me | Theorems.Thm_NonmonotoneLS_Global_sufficient_decrease
-- name    : NonmonotoneLS.Global.sufficient_decrease
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:26:05.440068+00:00
-- url     : https://prove2.me/theorems/03f03ddc-ef9d-48b1-bcb3-27907b5b93c3
-- title:
--   Eqs. (2.8)–(2.9) — $f_{k+1} \le C_k - \beta\|g_k\|^2$
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ be continuously differentiable and let $(x_k, d_k, \alpha_k, \eta_k)$ be a run of the nonmonotone line search algorithm with $g_k^{\mathsf T} d_k \le 0$ for every $k$, where $g_k = \nabla f(x_k)$. Let $c_1, c_2 > 0$ and $K \ge 0$ be such that
--   $$g_k^{\mathsf T} d_k \le -c_1\|g_k\|^2 \quad\text{and}\quad \|d_k\| \le c_2 \|g_k\| \qquad \text{for all } k \ge K,$$
--   and let $L > 0$ be such that $\nabla f$ is $L$-Lipschitz on the level set $\mathcal L$ (Wolfe rule) or on $\bar{\mathcal L}$ (Armijo rule). Then for all $k \ge K$
--
--   $$f_{k+1} \le C_k - \beta \|g_k\|^2, \qquad \beta = \min\left\{ \frac{\delta\mu c_1}{\rho},\ \frac{2\delta(1-\delta)c_1^2}{L\rho c_2^2},\ \frac{\delta(1-\sigma)c_1^2}{Lc_2^2} \right\}.$$
--
--   This uniform decrease of each new function value below the reference value is the core estimate of the global convergence proof: combined with the cost update (1.6) it gives $C_{k+1} \le C_k - \beta\|g_k\|^2/Q_{k+1}$.
--
--   **Formalization Note.** The paper writes (2.8) without a range of $k$; it holds where the direction assumption holds, which is how the proof uses it, so the statement carries an explicit threshold $K$. The hypothesis $g_k^{\mathsf T} d_k \le 0$ for every $k$ keeps all iterates in $\mathcal L$ (see Theorem 2.2). The constant $\beta$ is exactly (2.9).
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1047, Eqs. (2.8)–(2.9) (proof of Theorem 2.2)

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_Global_Run
import Definitions.Def_NonmonotoneLS_Global_Regions

open scoped InnerProductSpace NNReal Topology
open Filter

namespace NonmonotoneLS.Global

/-- Eqs. (2.8)–(2.9) (p. 1047): along a run with `∇f(x_k) d_k ≤ 0` for every `k`, if (2.4)–(2.5)
hold with constants `c₁, c₂ > 0` for all `k ≥ K` and `∇f` is `L`-Lipschitz (`L > 0`) on `𝓛`
(Wolfe) or on `𝓛̄` (Armijo), then `f(x_{k+1}) ≤ C_k - β ‖∇f(x_k)‖²` for all `k ≥ K`, with
`β = min{δμc₁/ρ, 2δ(1-δ)c₁²/(Lρc₂²), δ(1-σ)c₁²/(Lc₂²)}`. -/
theorem sufficient_decrease {n : ℕ} (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (K : ℕ)
    (hdir : ∀ k, K ≤ k →
      ⟪gradient f (x k), d k⟫_ℝ ≤ -c₁ * ‖gradient f (x k)‖ ^ 2 ∧
        ‖d k‖ ≤ c₂ * ‖gradient f (x k)‖)
    (L : ℝ≥0) (hL : 0 < L) (hLip : LipschitzHyp p r f x d L) :
    ∀ k, K ≤ k →
      f (x (k + 1)) ≤ Shared.costC f x η k -
        min (min (p.δ * p.μ * c₁ / p.ρ) (2 * p.δ * (1 - p.δ) * c₁ ^ 2 / ((L : ℝ) * p.ρ * c₂ ^ 2)))
            (p.δ * (1 - p.σ) * c₁ ^ 2 / ((L : ℝ) * c₂ ^ 2)) *
          ‖gradient f (x k)‖ ^ 2 := by sorry

end NonmonotoneLS.Global
