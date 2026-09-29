-- Prove2me | Theorems.Thm_NonmonotoneLS_Global_cost_bounds
-- name    : NonmonotoneLS.Global.cost_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:20:16.878353+00:00
-- url     : https://prove2.me/theorems/095cc96e-7db3-4a71-84b5-33861e46b34a
-- title:
--   Lemma 1.1 (bounds) — $f_k \le C_k \le A_k$
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ be continuously differentiable and let $(x_k, d_k, \alpha_k, \eta_k)$ be a run of the nonmonotone line search algorithm (with either the Wolfe or the Armijo rule). Write $f_k = f(x_k)$, let $C_k$ be the reference values of (1.6) and $A_k = \frac{1}{k+1}\sum_{i=0}^k f_i$. If $\nabla f(x_k) d_k \le 0$ for each $k$, then
--
--   $$f_k \le C_k \le A_k \qquad \text{for each } k.$$
--
--   The lower bound says that the nonmonotone reference value never falls below the current function value, so the line search at $x_k$ is well defined; the upper bound places $C_k$ below the running average of all previous function values.
--
--   **Formalization Note.** Only $\eta_k \in [0,1]$ and condition (1.4), which both rules impose, are used.
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1045, Lemma 1.1 (first sentence)

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_Global_Run
import Definitions.Def_NonmonotoneLS_Global_Regions

open scoped InnerProductSpace NNReal Topology
open Filter

namespace NonmonotoneLS.Global

/-- Lemma 1.1, first sentence (p. 1045): if `∇f(x_k) d_k ≤ 0` for each `k`, then along the run
`f(x_k) ≤ C_k ≤ A_k` for each `k`. -/
theorem cost_bounds {n : ℕ} (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0) :
    ∀ k, f (x k) ≤ Shared.costC f x η k ∧ Shared.costC f x η k ≤ Shared.avgA f x k := by sorry

end NonmonotoneLS.Global
