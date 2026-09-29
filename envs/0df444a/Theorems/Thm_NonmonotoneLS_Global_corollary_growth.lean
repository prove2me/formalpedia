-- Prove2me | Theorems.Thm_NonmonotoneLS_Global_corollary_growth
-- name    : NonmonotoneLS.Global.corollary_growth
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:29:34.664114+00:00
-- url     : https://prove2.me/theorems/a8dc2a3e-990e-49fb-aa1b-2c827178426a
-- title:
--   Corollary 2.3 — global convergence under the growth condition (2.16)
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ be continuously differentiable and bounded from below, and let $(x_k, d_k, \alpha_k, \eta_k)$ be a run of the nonmonotone line search algorithm with $\eta_{\max} < 1$ and $\nabla f(x_k) d_k \le 0$ for every $k$. Assume $\nabla f$ is Lipschitz continuous on the level set $\mathcal L$ if the Wolfe conditions are used, and on $\bar{\mathcal L}$ if the Armijo conditions are used. Suppose that for some $c_1 > 0$, (2.4) $g_k^{\mathsf T} d_k \le -c_1\|g_k\|^2$ holds for all sufficiently large $k$, and that for constants $\tau_1 > 0$, $\tau_2 \ge 0$
--
--   $$\|d_k\|^2 \le \tau_1 + \tau_2 k \qquad \text{for each } k. \qquad (2.16)$$
--
--   1. If $\tau_2 \ne 0$, then $\displaystyle\liminf_{k\to\infty} \|\nabla f(x_k)\| = 0$. (2.17)
--   2. If $\tau_2 = 0$, then $\displaystyle\lim_{k\to\infty} \|\nabla f(x_k)\| = 0$. (2.18)
--
--   The corollary replaces the bound $\|d_k\| \le c_2\|g_k\|$ of the direction assumption by a growth condition that allows the directions to become unbounded.
--
--   **Formalization Note.** The paper says "positive constants $\tau_1$ and $\tau_2$" but then treats $\tau_2 = 0$; the statement takes $\tau_1 > 0$, $\tau_2 \ge 0$. The $\liminf$ in (2.17) is stated as "for every $\varepsilon > 0$, $\|\nabla f(x_k)\| < \varepsilon$ for infinitely many $k$", which is equivalent for a nonnegative sequence and avoids the junk value of Lean's real $\liminf$ on divergent sequences. As in Theorem 2.2, $\nabla f(x_k) d_k \le 0$ is assumed for every $k$. When $\tau_2 > 0$ the directions may be unbounded, $d_{\max} = \infty$ and $\bar{\mathcal L} = \mathbb{R}^n$.
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1048, Corollary 2.3 with Eq. (2.16)

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_Global_Run
import Definitions.Def_NonmonotoneLS_Global_Regions

open scoped InnerProductSpace NNReal Topology
open Filter

namespace NonmonotoneLS.Global

/-- Corollary 2.3 (p. 1048). Suppose `η_max < 1`, `f` is continuously differentiable and bounded
from below, and `(x_k, d_k, α_k, η_k)` is a run of the NLSA with `∇f(x_k) d_k ≤ 0` for every `k`,
where `∇f` is Lipschitz on `𝓛` (Wolfe) or on `𝓛̄` (Armijo). Assume (2.4) for all sufficiently
large `k` and the growth condition (2.16) `‖d_k‖² ≤ τ₁ + τ₂ k` for each `k` (`τ₁ > 0`, `τ₂ ≥ 0`).
If `τ₂ ≠ 0` then `liminf ‖∇f(x_k)‖ = 0` (2.17); if `τ₂ = 0` then `‖∇f(x_k)‖ → 0` (2.18). -/
theorem corollary_growth {n : ℕ} (p : Shared.Params) (r : Rule)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (hbdd : BddBelow (Set.range f))
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η) (hηmax : p.ηmax < 1)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0)
    (c₁ : ℝ) (hc₁ : 0 < c₁)
    (hdir : ∀ᶠ k in atTop, ⟪gradient f (x k), d k⟫_ℝ ≤ -c₁ * ‖gradient f (x k)‖ ^ 2)
    (τ₁ τ₂ : ℝ) (hτ₁ : 0 < τ₁) (hτ₂ : 0 ≤ τ₂)
    (hgrowth : ∀ k : ℕ, ‖d k‖ ^ 2 ≤ τ₁ + τ₂ * k)
    (hLip : ∃ L : ℝ≥0, LipschitzHyp p r f x d L) :
    (τ₂ ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, ‖gradient f (x k)‖ < ε) ∧
      (τ₂ = 0 → Tendsto (fun k => ‖gradient f (x k)‖) atTop (𝓝 0)) := by sorry

end NonmonotoneLS.Global
