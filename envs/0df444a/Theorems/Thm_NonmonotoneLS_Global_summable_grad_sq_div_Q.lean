-- Prove2me | Theorems.Thm_NonmonotoneLS_Global_summable_grad_sq_div_Q
-- name    : NonmonotoneLS.Global.summable_grad_sq_div_Q
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:27:19.109639+00:00
-- url     : https://prove2.me/theorems/7d941d48-5ec7-426e-96e2-b6296d9775df
-- title:
--   Eq. (2.14) — $\sum_k \|g_k\|^2 / Q_{k+1} < \infty$
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ be continuously differentiable and bounded from below, and let $(x_k, d_k, \alpha_k, \eta_k)$ be a run of the nonmonotone line search algorithm with $\nabla f(x_k) d_k \le 0$ for every $k$ that satisfies the direction assumption (2.4)–(2.5). Assume $\nabla f$ is Lipschitz continuous on the level set $\mathcal L$ if the Wolfe conditions are used, and on $\bar{\mathcal L}$ if the Armijo conditions are used. Then, with $g_k = \nabla f(x_k)$ and $Q_k$ from (1.6),
--
--   $$\sum_{k=0}^{\infty} \frac{\|g_k\|^2}{Q_{k+1}} < \infty.$$
--
--   Both conclusions of Theorem 2.2 follow from this series bound and the growth bounds $Q_{k+1} \le k+2$ of (1.8) and $Q_{k+1} \le 1/(1-\eta_{\max})$ of (2.15).
--
--   **Formalization Note.** The terms are nonnegative ($Q_{k+1} \ge 1$ along a run), so summability in Lean is the paper's "$< \infty$". The hypothesis $\nabla f(x_k) d_k \le 0$ for every $k$ is the repair discussed in Theorem 2.2.
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1048, Eq. (2.14) (proof of Theorem 2.2)

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_Global_Run
import Definitions.Def_NonmonotoneLS_Global_Regions

open scoped InnerProductSpace NNReal Topology
open Filter

namespace NonmonotoneLS.Global

/-- Eq. (2.14) (p. 1048): under the hypotheses of Theorem 2.2 (with `∇f(x_k) d_k ≤ 0` for every
`k`), `∑_{k=0}^∞ ‖∇f(x_k)‖² / Q_{k+1} < ∞`. -/
theorem summable_grad_sq_div_Q {n : ℕ} (p : Shared.Params) (r : Rule)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (hbdd : BddBelow (Set.range f))
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0)
    (hdir : DirectionAssumption f x d)
    (hLip : ∃ L : ℝ≥0, LipschitzHyp p r f x d L) :
    Summable (fun k => ‖gradient f (x k)‖ ^ 2 / Shared.costQ η (k + 1)) := by sorry

end NonmonotoneLS.Global
