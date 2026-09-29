-- Prove2me | Theorems.Thm_NonmonotoneLS_RLinear_suboptimality_le_gamma_grad_sq
-- name    : NonmonotoneLS.RLinear.suboptimality_le_gamma_grad_sq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:30:46.721236+00:00
-- url     : https://prove2.me/theorems/bba77de8-afb5-4b23-ad39-c4c58f83a95a
-- title:
--   Eq. (3.4) — $f(x) - f(x^*) \le \gamma \|\nabla f(x)\|^2$
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ be continuously differentiable and strongly convex with constant $\gamma > 0$ in the sense of (3.1):
--
--   $$f(x) \ge f(y) + \nabla f(y)(x - y) + \frac{1}{2\gamma}\|x - y\|^2 \quad \text{for all } x, y.$$
--
--   If $x^*$ minimizes $f$, then for every $x \in \mathbb{R}^n$
--
--   $$f(x) - f(x^*) \le \gamma \|\nabla f(x)\|^2. \quad (3.4)$$
--
--   The bound turns the size of the gradient into a bound on the optimality gap; it is used in Case 2 of the contraction (3.8).
--
--   **Formalization Note.** $x^*$ is any global minimizer ($f(x^*) \le f(y)$ for all $y$); uniqueness follows from (3.1) and is not assumed. The platform theorem `ConvexOptimization.strong_convexity_quadratic_lower_bound` (a reference item of this mission) gives the stronger bound $\frac{\gamma}{2}\|\nabla f(x)\|^2$ with $m = 1/\gamma$; this item keeps the paper's constant $\gamma$.
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1049, Eq. (3.4)

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

/-- Eq. (3.4) (p. 1049): if `f` is strongly convex in the sense of (3.1) with constant `γ` and
`x*` minimizes `f`, then `f(x) - f(x*) ≤ γ ‖∇f(x)‖²` for every `x`. -/
theorem suboptimality_le_gamma_grad_sq {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (γ : ℝ) (hsc : IsStronglyConvexWith f γ)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y) :
    ∀ y, f y - f xstar ≤ γ * ‖gradient f y‖ ^ 2 := by sorry

end NonmonotoneLS.RLinear
