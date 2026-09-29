-- Prove2me | Theorems.Thm_NonmonotoneLS_RLinear_r_linear_convergence
-- name    : NonmonotoneLS.RLinear.r_linear_convergence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:52:34.142749+00:00
-- url     : https://prove2.me/theorems/b5b576a0-14b1-4cf1-9a8f-72841357ad23
-- title:
--   Theorem 3.1 — R-linear convergence of the nonmonotone line search for strongly convex $f$
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ be continuously differentiable and strongly convex: there is $\gamma > 0$ with
--
--   $$f(x) \ge f(y) + \nabla f(y)(x - y) + \frac{1}{2\gamma}\|x - y\|^2 \quad \text{for all } x, y \in \mathbb{R}^n, \quad (3.1)$$
--
--   and let $x^*$ be its minimizer. Consider a run of the Nonmonotone Line Search Algorithm (Wolfe or Armijo rule, parameters $0 \le \eta_{\min} \le \eta_{\max} \le 1$, $0 < \delta < \sigma < 1 < \rho$, $\mu > 0$) with iterates $x_k$, directions $d_k$ and steps $\alpha_k$, and write $g_k = \nabla f(x_k)$. Assume
--
--   1. the direction assumption holds at every iteration: there are $c_1, c_2 > 0$ with $g_k^{\mathsf T} d_k \le -c_1\|g_k\|^2$ and $\|d_k\| \le c_2\|g_k\|$ for every $k \ge 0$;
--   2. $\alpha_k \le \mu$ for all $k$;
--   3. $\eta_{\max} < 1$;
--   4. $\nabla f$ is Lipschitz continuous on bounded sets.
--
--   Then there exists $\theta \in (0, 1)$ such that
--
--   $$f(x_k) - f(x^*) \le \theta^k \big(f(x_0) - f(x^*)\big) \quad \text{for each } k. \quad (3.5)$$
--
--   This is the paper's second main result: with averaged reference values the nonmonotone line search keeps the linear rate of monotone descent methods on strongly convex functions.
--
--   **Formalization Note.** (i) *Repair of the printed statement.* The paper's direction assumption holds only "for all sufficiently large $k$", but the conclusion is claimed for each $k$, and the proof applies (2.4)–(2.5) at every $k$. As printed the theorem is false: with $d_0 = 0$ the step $\alpha_0 = 1$ satisfies the Wolfe conditions with equality, $x_1 = x_0$, and (3.5) at $k = 1$ fails whenever $x_0 \ne x^*$. The direction assumption is therefore required for every $k \ge 0$; descent at every $k$ follows from (2.4). (ii) *The step bound.* "There exists $\mu > 0$ such that $\alpha_k \le \mu$ for all $k$" is stated as $\alpha_k \le \mu$ with $\mu$ the algorithm's parameter. This loses nothing: an Armijo run satisfies $\alpha_k \le \mu$ by its rule, and a Wolfe run does not use $\mu$, so a Wolfe run with $\alpha_k \le \mu'$ is a run for the parameters with $\mu := \mu'$. The proof's region $\bar{\mathcal L}$ and constant $\beta$ use the same $\mu$. (iii) $x^*$ is any global minimizer; uniqueness follows from (3.1). (iv) "Lipschitz continuous on bounded sets" is: for every bounded $S$ there is $L$ with $\nabla f$ $L$-Lipschitz on $S$. (v) $\theta$ may depend on $f$, the parameters and the run, as in the proof.
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1049, Theorem 3.1, Eq. (3.5)

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

/-- Theorem 3.1 (p. 1049), with the direction assumption required at every `k` (repair (b)):
if `f` is strongly convex in the sense of (3.1), `x*` minimizes `f`, the directions of the run
satisfy (2.4)–(2.5) for every `k`, the steps satisfy `α_k ≤ μ` for all `k`, `η_max < 1`, and `∇f`
is Lipschitz continuous on bounded sets, then there is `θ ∈ (0, 1)` with
`f(x_k) - f(x*) ≤ θ^k (f(x_0) - f(x*))` for each `k`. -/
theorem r_linear_convergence {n : ℕ} (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (γ : ℝ) (hsc : IsStronglyConvexWith f γ)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y)
    (hηmax : p.ηmax < 1)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (hdir : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ DirectionBounds f x d c₁ c₂)
    (hαμ : ∀ k, α k ≤ p.μ)
    (hLip : ∀ S : Set (EuclideanSpace ℝ (Fin n)), Bornology.IsBounded S →
      ∃ L : ℝ≥0, LipschitzOnWith L (gradient f) S) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∀ k, f (x k) - f xstar ≤ θ ^ k * (f (x 0) - f xstar) := by sorry

end NonmonotoneLS.RLinear
