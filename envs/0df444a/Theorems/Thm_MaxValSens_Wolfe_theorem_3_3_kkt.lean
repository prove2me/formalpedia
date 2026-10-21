-- Prove2me | Theorems.Thm_MaxValSens_Wolfe_theorem_3_3_kkt
-- name    : MaxValSens.Wolfe.theorem_3_3_kkt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:14.723334+00:00
-- url     : https://prove2.me/theorems/20dcda58-705f-4cad-95fd-7581f0e1b960
-- title:
--   Proof of Theorem 3.3 (i), p. 17 — KKT conditions for (3.16) under a CQ (local error bound)
-- statement:
--   Let $f$ and $g$ be twice continuously differentiable, $\xi\in\mathbb R^n$ and $\epsilon>0$. Suppose $(\bar x,\bar y,\bar\lambda)$ is a local minimizer of problem (3.16),
--   $$\min_{x,y,\lambda}\ \mathcal L(x,y,\lambda)-\xi^\top(x-\bar x)+\epsilon\|x-\bar x\|\quad\text{s.t.}\quad\nabla_y\mathcal L(x,y,\lambda)=0,\ \lambda\ge0,$$
--   and that a CQ — the local error bound of the constraint system (3.11) — holds at $(\bar x,\bar y,\bar\lambda)$. Then $(\bar x,\bar y,\bar\lambda)$ is a KKT point of (3.16): there is $u\in\mathbb R^m$ with
--
--   $$\xi\in\nabla_x\mathcal L(\bar x,\bar y,\bar\lambda)+\epsilon\mathbb B+\nabla^2_{xy}\mathcal L(\bar x,\bar y,\bar\lambda)u,\qquad u\in\Xi^1(\bar x,\bar y,\bar\lambda),$$
--
--   that is, $\nabla^2_{yy}\mathcal L(\bar x,\bar y,\bar\lambda)u=0$ and $0\le-\nabla_yg(\bar x,\bar y)^\top u-g(\bar x,\bar y)\perp\bar\lambda\ge0$. Here $\mathbb B$ is the closed unit ball.
--
--   This is the multiplier rule for the nonsmooth problem (3.16) that produces the set on the right of (3.12).
--
--   **Formalization Note** "A CQ" is read as the local error bound `LocalErrorBound311`, weaker than each CQ the paper lists (p. 8). The inclusion $\xi\in\cdots+\epsilon\mathbb B$ is written $\|\xi-(\nabla_x\mathcal L+\nabla^2_{xy}\mathcal L\,u)\|\le\epsilon$ with the Euclidean norm. Convexity is not assumed.
-- source:
--   Guo, Ye, Zhang, Sensitivity analysis of the maximal value function with applications in nonconvex minimax programs, arXiv:2303.01474v1, p. 17, proof of Theorem 3.3 (i), after (3.16)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MaxValSens_Wolfe_Setting
open Filter Topology
open scoped InnerProductSpace

namespace MaxValSens.Wolfe

/-- Proof of Theorem 3.3 (i), p. 17: if `(x̄, ȳ, λ̄)` is a local minimizer of problem (3.16)
and a CQ (the local error bound) holds there for the system (3.11), then it is a KKT point of
(3.16): there is `u ∈ Ξ¹(x̄, ȳ, λ̄)` with `ξ ∈ ∇_x L(x̄, ȳ, λ̄) + ε𝔹 + ∇²_xy L(x̄, ȳ, λ̄) u`. -/
theorem theorem_3_3_kkt {n m q : ℕ} (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ)
    (xbar : E n) (ybar : E m) (lambar : Fin q → ℝ) (ξ : E n) (ε : ℝ)
    (hf : ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2))
    (hg : ∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2)) (hε : 0 < ε)
    (hmin : IsLocalMinOn
      (fun z : E n × E m × (Fin q → ℝ) =>
        Lag 1 f g z.1 z.2.1 z.2.2 - ⟪ξ, z.1 - xbar⟫_ℝ + ε * ‖z.1 - xbar‖)
      (Sys311 f g) (xbar, ybar, lambar))
    (hCQ : LocalErrorBound311 f g (xbar, ybar, lambar)) :
    ∃ u ∈ Xi 1 f g xbar ybar lambar,
      ‖ξ - (gradX f g xbar ybar lambar + hessXY f g xbar ybar lambar u)‖ ≤ ε := by sorry

end MaxValSens.Wolfe
