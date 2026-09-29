-- Prove2me | Theorems.Thm_NonmonotoneLS_RLinear_cost_bounds
-- name    : NonmonotoneLS.RLinear.cost_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:26:17.623504+00:00
-- url     : https://prove2.me/theorems/967197d5-4789-437f-9371-917b9ba4899f
-- title:
--   Lemma 1.1 (bounds) — $f_k \le C_k \le A_k$
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ be continuously differentiable and consider a run of the Nonmonotone Line Search Algorithm (Wolfe or Armijo rule) with iterates $x_k$, directions $d_k$, reference values $C_k$ of (1.6) and averages $A_k = \frac{1}{k+1}\sum_{i=0}^k f(x_i)$. If $\nabla f(x_k) d_k \le 0$ for each $k$, then
--
--   $$f(x_k) \le C_k \le A_k \qquad \text{for each } k.$$
--
--   So $C_k$ always lies between the current function value and the average of all function values so far; in particular the line search update is well defined.
--
--   **Formalization Note.** Only the first sentence of Lemma 1.1 is stated; the existence part is in the companion mission. The standing assumption that $f$ is continuously differentiable is made explicit.
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1045, Lemma 1.1 (first sentence)

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

/-- Lemma 1.1, first sentence (p. 1045): if `∇f(x_k) d_k ≤ 0` for each `k`, then along the run
`f(x_k) ≤ C_k ≤ A_k` for each `k`. -/
theorem cost_bounds {n : ℕ} (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0) :
    ∀ k, f (x k) ≤ Shared.costC f x η k ∧ Shared.costC f x η k ≤ Shared.avgA f x k := by sorry

end NonmonotoneLS.RLinear
