-- Prove2me | Theorems.Thm_NonmonotoneLS_RLinear_cost_contraction
-- name    : NonmonotoneLS.RLinear.cost_contraction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:48:49.499514+00:00
-- url     : https://prove2.me/theorems/4b548d93-53d3-45f3-992f-a62ef6ffed46
-- title:
--   Eq. (3.8) — $C_{k+1} - f(x^*) \le \theta(C_k - f(x^*))$
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ be continuously differentiable and strongly convex with constant $\gamma > 0$ in the sense of (3.1), and let $x^*$ minimize $f$. Consider a run of the Nonmonotone Line Search Algorithm with $\eta_{\max} < 1$, iterates $x_k$, directions $d_k$, steps $\alpha_k$ and reference values $C_k$; write $g_k = \nabla f(x_k)$. Assume
--
--   1. there are $c_1, c_2 > 0$ with $g_k^{\mathsf T} d_k \le -c_1\|g_k\|^2$ and $\|d_k\| \le c_2\|g_k\|$ for every $k$;
--   2. $\alpha_k \le \mu$ for every $k$;
--   3. $\nabla f$ is Lipschitz continuous with constant $L > 0$ on $\bar{\mathcal L}$.
--
--   Then for each $k$
--
--   $$C_{k+1} - f(x^*) \le \theta\,(C_k - f(x^*)), \quad (3.8)$$
--
--   where
--
--   $$\theta = 1 - \beta b_2 (1 - \eta_{\max}), \qquad b_2 = \frac{1}{\beta + \gamma b^2},$$
--
--   $\beta$ is given by (2.9) and $b = 1 + \mu c_2 L$ by (3.7).
--
--   Since $f(x_k) \le C_k$ and $C_0 = f(x_0)$, the contraction yields the linear rate (3.5) immediately.
--
--   **Formalization Note.** All constants are explicit and computed from $\delta, \sigma, \rho, \mu, \eta_{\max}, c_1, c_2, L, \gamma$. The direction assumption is required at every $k$, as in the goal theorem.
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1050, Eq. (3.8)

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_RLinear_Run
import Definitions.Def_NonmonotoneLS_RLinear_Regions
import Definitions.Def_NonmonotoneLS_RLinear_Constants

open scoped InnerProductSpace NNReal
open Filter

namespace NonmonotoneLS.RLinear

/-- Eq. (3.8) (p. 1050): if `f` is strongly convex in the sense of (3.1) with constant `γ`,
`x*` minimizes `f`, `η_max < 1`, the directions satisfy (2.4)–(2.5) with constants `c₁, c₂ > 0` at
every `k`, the steps satisfy `α_k ≤ μ`, and `∇f` is `L`-Lipschitz (`L > 0`) on `𝓛̄`, then
`C_{k+1} - f(x*) ≤ θ (C_k - f(x*))` for every `k`, where `θ = 1 - βb₂(1 - η_max)`,
`b₂ = 1/(β + γb²)`, `β` is given by (2.9) and `b = 1 + μc₂L`. -/
theorem cost_contraction {n : ℕ} (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (γ : ℝ) (hsc : IsStronglyConvexWith f γ)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y)
    (hηmax : p.ηmax < 1)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hdir : DirectionBounds f x d c₁ c₂)
    (hαμ : ∀ k, α k ≤ p.μ)
    (L : ℝ≥0) (hL : 0 < L) (hLip : LipschitzOnWith L (gradient f) (Lbar p f x d)) :
    ∀ k, Shared.costC f x η (k + 1) - f xstar ≤
      theta p c₁ c₂ L γ * (Shared.costC f x η k - f xstar) := by sorry

end NonmonotoneLS.RLinear
