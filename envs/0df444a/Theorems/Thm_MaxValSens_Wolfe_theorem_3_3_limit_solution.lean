-- Prove2me | Theorems.Thm_MaxValSens_Wolfe_theorem_3_3_limit_solution
-- name    : MaxValSens.Wolfe.theorem_3_3_limit_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:15.931957+00:00
-- url     : https://prove2.me/theorems/74f148e4-59f3-4d67-a244-760221721d86
-- title:
--   Proof of Theorem 3.3 (ii), pp. 17–18 — solutions yᵏ ∈ S(xᵏ) converge to some ỹ ∈ S(x̄) under restricted sup-compactness
-- statement:
--   Assume the standing assumption of §3.2 at $\bar x$ and the restricted sup-compactness condition at $\bar x$. Let $x^k\to\bar x$ with $V(x^k)\to V(\bar x)$. Then, after passing to a subsequence $x^{k_j}$, there are optimal solutions $y^j\in\mathcal S(x^{k_j})$ and a point $\tilde y$ with
--
--   $$y^j\to\tilde y\qquad\text{and}\qquad\tilde y\in\mathcal S(\bar x).$$
--
--   This produces the solution $\tilde y$ of $(P_{\bar x})$ around which the limiting estimates (3.13)–(3.14) are taken.
--
--   **Formalization Note** The subsequence is a strictly increasing $\varphi:\mathbb N\to\mathbb N$; convergence $V(x^k)\to V(\bar x)$ is in `EReal`.
-- source:
--   Guo, Ye, Zhang, Sensitivity analysis of the maximal value function with applications in nonconvex minimax programs, arXiv:2303.01474v1, pp. 17–18, proof of Theorem 3.3 (ii)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MaxValSens_Wolfe_Setting
open Filter Topology
open scoped InnerProductSpace

namespace MaxValSens.Wolfe

/-- Proof of Theorem 3.3 (ii), pp. 17–18: under restricted sup-compactness at `x̄`, if
`xₖ → x̄` and `V(xₖ) → V(x̄)`, then along a subsequence there are `yₖ ∈ S(xₖ)` converging to
some `ỹ ∈ S(x̄)`. -/
theorem theorem_3_3_limit_solution {n m q : ℕ} (f : E n → E m → ℝ)
    (g : Fin q → E n → E m → ℝ) (xbar : E n)
    (hS : Standing f g xbar) (hRSC : RestrictedSupCompact f g xbar)
    (xs : ℕ → E n) (hx : Tendsto xs atTop (𝓝 xbar))
    (hV : Tendsto (fun k => V f g (xs k)) atTop (𝓝 (V f g xbar))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ys : ℕ → E m, (∀ k, ys k ∈ S f g (xs (φ k))) ∧
      ∃ ytil ∈ S f g xbar, Tendsto ys atTop (𝓝 ytil) := by sorry

end MaxValSens.Wolfe
