-- Prove2me | Theorems.Thm_NonmonotoneLS_RLinear_grad_norm_growth
-- name    : NonmonotoneLS.RLinear.grad_norm_growth
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:39:08.170983+00:00
-- url     : https://prove2.me/theorems/4ea3e885-91c4-4cbf-9386-7384a1669a5f
-- title:
--   Eq. (3.7) — $\|g_{k+1}\| \le b\|g_k\|$ with $b = 1 + \mu c_2 L$
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ be continuously differentiable and consider a run of the Nonmonotone Line Search Algorithm with iterates $x_k$, directions $d_k$ and steps $\alpha_k$; write $g_k = \nabla f(x_k)$. Assume there are $c_1, c_2 > 0$ with $g_k^{\mathsf T} d_k \le -c_1\|g_k\|^2$ and $\|d_k\| \le c_2\|g_k\|$ for every $k$, that $\alpha_k \le \mu$ for every $k$, and that $\nabla f$ is Lipschitz continuous with constant $L \ge 0$ on $\bar{\mathcal L}$. Then for every $k$
--
--   $$\|g_{k+1}\| \le b\|g_k\|, \qquad b = 1 + \mu c_2 L. \quad (3.7)$$
--
--   The gradient cannot grow by more than a fixed factor in one step; combined with (3.4) this bounds $f(x_{k+1}) - f(x^*)$ by $\gamma b^2\|g_k\|^2$ in Case 2 of (3.8).
--
--   **Formalization Note.** The Lipschitz bound is used only between $x_k$ and $x_{k+1}$, both in $\mathcal L \subseteq \bar{\mathcal L}$ (they lie in $\mathcal L$ because (2.4) gives descent). $L = 0$ is allowed.
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1050, Eq. (3.7)

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

/-- Eq. (3.7) (p. 1050): along a run whose directions satisfy (2.4)–(2.5) with constants
`c₁, c₂ > 0` at every `k`, whose steps satisfy `α_k ≤ μ`, and for which `∇f` is `L`-Lipschitz on
`𝓛̄`, `‖∇f(x_{k+1})‖ ≤ b ‖∇f(x_k)‖` for every `k`, with `b = 1 + μc₂L`. -/
theorem grad_norm_growth {n : ℕ} (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hdir : DirectionBounds f x d c₁ c₂)
    (hαμ : ∀ k, α k ≤ p.μ)
    (L : ℝ≥0) (hLip : LipschitzOnWith L (gradient f) (Lbar p f x d)) :
    ∀ k, ‖gradient f (x (k + 1))‖ ≤ bConst p c₂ L * ‖gradient f (x k)‖ := by sorry

end NonmonotoneLS.RLinear
