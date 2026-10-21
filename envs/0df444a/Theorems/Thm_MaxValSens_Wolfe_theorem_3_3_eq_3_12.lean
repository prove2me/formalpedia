-- Prove2me | Theorems.Thm_MaxValSens_Wolfe_theorem_3_3_eq_3_12
-- name    : MaxValSens.Wolfe.theorem_3_3_eq_3_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:15.645748+00:00
-- url     : https://prove2.me/theorems/7cfaa753-6c3d-4a22-b3f0-e31c3a0440db
-- title:
--   Theorem 3.3 (3.12), pp. 16–17 — regular subdifferential of the maximal value function via the Wolfe dual multipliers
-- statement:
--   Assume the standing assumption of §3.2 at $\bar x$ ($f,g$ of class $C^2$; $f(x,\cdot)$ concave and $g_i(x,\cdot)$ convex for $x$ near $\bar x$). Let $\bar y\in\mathcal S(\bar x)$ and $\bar\lambda\in\Sigma(\bar x,\bar y)$, and suppose a CQ holds at $(\bar x,\bar y,\bar\lambda)$ for the constraint system
--   $$\nabla_y\mathcal L(x,y,\lambda)=0,\quad\lambda\ge0 \tag{3.11}$$
--   in $(x,y,\lambda)$. Then the regular subdifferential of the maximal value function satisfies
--
--   $$\widehat\partial V(\bar x)\subseteq\big\{\nabla_x\mathcal L(\bar x,\bar y,\bar\lambda)+\nabla^2_{xy}\mathcal L(\bar x,\bar y,\bar\lambda)u:\ u\in\Xi^1(\bar x,\bar y,\bar\lambda)\big\}. \tag{3.12}$$
--
--   The estimate needs only one solution $\bar y$ and one multiplier $\bar\lambda$, and is the pointwise ingredient of the limiting estimates (3.13)–(3.14).
--
--   **Formalization Note** "A CQ" is the local error bound of (3.11) (`LocalErrorBound311`). $\widehat\partial V(\bar x)$ is the set of `IsRegularSubgrad (V f g) xbar ξ`, which requires $V(\bar x)<+\infty$; here $V(\bar x)=f(\bar x,\bar y)$ is finite.
-- source:
--   Guo, Ye, Zhang, Sensitivity analysis of the maximal value function with applications in nonconvex minimax programs, arXiv:2303.01474v1, pp. 16–17, Theorem 3.3, (3.11)–(3.12)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MaxValSens_Wolfe_Setting
open Filter Topology
open scoped InnerProductSpace

namespace MaxValSens.Wolfe

/-- Theorem 3.3, first assertion (3.12), pp. 16–17: if `ȳ ∈ S(x̄)`, `λ̄ ∈ Σ(x̄, ȳ)` and a CQ
(the local error bound) holds at `(x̄, ȳ, λ̄)` for (3.11), then
`∂̂V(x̄) ⊆ {∇_x L(x̄, ȳ, λ̄) + ∇²_xy L(x̄, ȳ, λ̄) u : u ∈ Ξ¹(x̄, ȳ, λ̄)}`. -/
theorem theorem_3_3_eq_3_12 {n m q : ℕ} (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ)
    (xbar : E n) (ybar : E m) (lambar : Fin q → ℝ)
    (hS : Standing f g xbar) (hy : ybar ∈ S f g xbar) (hlam : lambar ∈ SigmaM 1 f g xbar ybar)
    (hCQ : LocalErrorBound311 f g (xbar, ybar, lambar)) :
    {ξ | NonconvexSplitting.Shared.IsRegularSubgrad (V f g) xbar ξ} ⊆
      {ξ | ∃ u ∈ Xi 1 f g xbar ybar lambar,
        ξ = gradX f g xbar ybar lambar + hessXY f g xbar ybar lambar u} := by sorry

end MaxValSens.Wolfe
