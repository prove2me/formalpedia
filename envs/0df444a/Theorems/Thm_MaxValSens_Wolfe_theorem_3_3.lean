-- Prove2me | Theorems.Thm_MaxValSens_Wolfe_theorem_3_3
-- name    : MaxValSens.Wolfe.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:41.400126+00:00
-- url     : https://prove2.me/theorems/cbbe68f3-b913-41d7-afde-0f59461ffebe
-- title:
--   Theorem 3.3 (3.13)–(3.14), pp. 16–17 — limiting and horizon subdifferentials of the maximal value function, estimated over the union of optimal solutions
-- statement:
--   Consider the parametric maximization problem $(P_x)$: $\max_y f(x,y)$ s.t. $g(x,y)\le0$, with maximal value function $V$, solution map $\mathcal S$, Lagrangian $\mathcal L(x,y,\lambda)=f(x,y)-g(x,y)^\top\lambda$, multiplier sets $\Sigma(x,y)$ of $(P_x)$ and $\Xi^r(x,y,\lambda)$ of the Wolfe dual. Assume the standing assumption of §3.2 at $\bar x$: $f$ and every $g_i$ are $C^2$ in $(x,y)$, and $f(x,\cdot)$ is concave and every $g_i(x,\cdot)$ convex for all $x$ near $\bar x$. Suppose that
--
--   1. the restricted sup-compactness condition holds at $\bar x$;
--   2. a stable parametric CQ holds for $(P_{\bar x})$ at every $y\in\mathcal S(\bar x)$;
--   3. a stable CQ holds for the constraint system $\nabla_y\mathcal L(x,y,\lambda)=0,\ \lambda\ge0$ (3.11) at every $(\bar x,\tilde y,\tilde\lambda)$ with $\tilde y\in\mathcal S(\bar x)$ and $\tilde\lambda\in\Sigma(\bar x,\tilde y)$.
--
--   Then the limiting and horizon subdifferentials of $V$ at $\bar x$ satisfy
--
--   $$\partial V(\bar x)\subseteq\bigcup_{y\in\mathcal S(\bar x)}\big\{\nabla_x\mathcal L(\bar x,y,\lambda)+\nabla^2_{xy}\mathcal L(\bar x,y,\lambda)u:\ u\in\Xi^1(\bar x,y,\lambda),\ \lambda\in\Sigma(\bar x,y)\big\}, \tag{3.13}$$
--
--   $$\partial^\infty V(\bar x)\subseteq\bigcup_{y\in\mathcal S(\bar x)}\big\{\nabla^2_{xy}\mathcal L(\bar x,y,\lambda)u:\ u\in\Xi^0(\bar x,y,\lambda),\ \lambda\in\Sigma(\bar x,y)\big\}. \tag{3.14}$$
--
--   The estimates hold without local Lipschitz continuity of $V$, without inner semicontinuity of $\mathcal S$, and without a convex hull over the optimal solutions; they are the basis of the paper's optimality conditions for nonconvex minimax programs.
--
--   **Formalization Note** $V$ is `EReal`-valued; $\partial V$ is `NonconvexSplitting.Shared.LimitingSubdiff` and $\partial^\infty V$ is `HorizonSubdiff`, both built from regular subgradients. "Stable CQ" for (3.11) is `StableCQ311`: the local error bound at every feasible point near $(\bar x,\tilde y,\tilde\lambda)$ plus Definition 2.3(ii) for the multiplier set (2.3) of (3.11). "Stable parametric CQ" is `StableParamCQ`: Definition 2.3 with (i) read for feasible local maximizers of $(P_x)$, $(x,y)$ near $(\bar x,y)$. As printed, (3.14) uses $\Xi^0$ but $\Sigma=\Sigma^1$ and $\mathcal L=\mathcal L^1$.
-- source:
--   Guo, Ye, Zhang, Sensitivity analysis of the maximal value function with applications in nonconvex minimax programs, arXiv:2303.01474v1, pp. 16–17, Theorem 3.3, (3.13)–(3.14)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MaxValSens_Wolfe_Setting
open Filter Topology
open scoped InnerProductSpace

namespace MaxValSens.Wolfe

/-- Theorem 3.3, second assertion (3.13)–(3.14), p. 17: under restricted sup-compactness at
`x̄`, a stable parametric CQ for `(P_x̄)` at every `y ∈ S(x̄)`, and a stable CQ for (3.11) at every
`(x̄, ỹ, λ̃)` with `ỹ ∈ S(x̄)`, `λ̃ ∈ Σ(x̄, ỹ)`, the limiting and horizon subdifferentials of the
maximal value function satisfy (3.13) and (3.14). -/
theorem theorem_3_3 {n m q : ℕ} (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ) (xbar : E n)
    (hS : Standing f g xbar) (hRSC : RestrictedSupCompact f g xbar)
    (hPCQ : ∀ y ∈ S f g xbar, StableParamCQ f g xbar y)
    (hCQ : ∀ y ∈ S f g xbar, ∀ lam ∈ SigmaM 1 f g xbar y, StableCQ311 f g (xbar, y, lam)) :
    NonconvexSplitting.Shared.LimitingSubdiff (V f g) xbar ⊆
      {ξ | ∃ y ∈ S f g xbar, ∃ lam ∈ SigmaM 1 f g xbar y, ∃ u ∈ Xi 1 f g xbar y lam,
        ξ = gradX f g xbar y lam + hessXY f g xbar y lam u} ∧
    HorizonSubdiff (V f g) xbar ⊆
      {ξ | ∃ y ∈ S f g xbar, ∃ lam ∈ SigmaM 1 f g xbar y, ∃ u ∈ Xi 0 f g xbar y lam,
        ξ = hessXY f g xbar y lam u} := by sorry

end MaxValSens.Wolfe
