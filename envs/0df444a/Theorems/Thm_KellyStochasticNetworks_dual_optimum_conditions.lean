-- Prove2me | Theorems.Thm_KellyStochasticNetworks_dual_optimum_conditions
-- name    : KellyStochasticNetworks.dual_optimum_conditions
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T15:45:25.560018+00:00
-- url     : https://prove2.me/theorems/d0eea26c-ef75-46c2-b6cb-715ad18a247a
-- title:
--   Theorem 3.10 — a minimizer of the Dual problem satisfies the conditions on $B$
-- statement:
--   Section 3.4 looks for the mode of the equilibrium distribution (3.3) and, after Stirling's
--   approximation and a continuous relaxation, arrives at the **Primal** problem (3.4): maximize
--   $\sum_r (x_r\log\nu_r - x_r\log x_r + x_r)$ over $x \ge 0$ subject to $Ax \le C$. Its Lagrangian
--   dual is the **Dual** problem (3.5):
--   $$\text{minimize}\quad \sum_r \nu_r e^{-\sum_j y_j A_{jr}} + \sum_j y_j C_j
--     \qquad\text{over } y \ge 0 .$$
--
--   Let $y \ge 0$ minimize this objective over the positive orthant. Then for every link $j$,
--   $$\sum_r A_{jr}\,\nu_r\,e^{-\sum_i y_i A_{ir}}
--     \begin{cases} = C_j & \text{if } y_j > 0,\\[2pt] \le C_j & \text{if } y_j = 0.\end{cases}$$
--
--   Under the substitution $1 - B_j = e^{-y_j}$ these are precisely the **conditions on $B$**,
--   equation (3.6), of Theorem 3.10, and they have a fluid-flow reading: $\nu_r\prod_i(1-B_i)^{A_{ir}}$
--   is the arrival stream on route $r$ thinned once for each circuit it requests from each link, so
--   the left-hand side is the aggregate flow on link $j$; the conditions say that flow never
--   exceeds the link's capacity, and that blocking occurs only on links running at full capacity.
--
--   The book obtains them exactly this way — the Dual objective is convex and differentiable and
--   grows to infinity in each coordinate, so its minimum over $y \ge 0$ is attained, and at the
--   minimum the partial derivative in $y_j$ vanishes if $y_j > 0$ and is non-negative if $y_j = 0$.
--   This is what establishes the existence of a vector $B$ satisfying (3.6) without appealing to
--   the strong Lagrangian principle.
--
--   **Formalization Note** Minimality is stated directly as the defining inequality over the
--   positive orthant rather than through an optimization predicate, and the conclusion is the
--   displayed pair of conditions rather than a statement about a derivative, so no differentiability
--   API is presupposed. The incidence matrix has non-negative integer entries, the general case of
--   section 3.3.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, pp. 58-60 (PDF pp. 66-68), the Dual problem (3.5), the conditions on B (3.6), and Theorem 3.10: 'the minimum over y >= 0 will be at a point where sum_r A_{jr} nu_r e^{-sum_i y_i A_{ir}} = C_j if y_j > 0, <= C_j if y_j = 0. Note that these are precisely the conditions on B, under the substitution B_j = 1 - e^{-y_j}; this gives the existence of a solution to the conditions on B, and establishes the one-to-one correspondence with the optima of the Dual problem.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_KellyStochasticNetworks_Migration
import Definitions.Def_KellyStochasticNetworks_LossNetwork

namespace KellyStochasticNetworks

theorem dual_optimum_conditions {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r) (y : Fin J → ℝ) (hy : ∀ j, 0 ≤ y j)
    (hmin : ∀ z : Fin J → ℝ, (∀ j, 0 ≤ z j) → dualObjective A ν C y ≤ dualObjective A ν C z) :
    ∀ j, (0 < y j →
            (∑ r, (A j r : ℝ) * ν r * Real.exp (-∑ i, y i * (A i r : ℝ))) = (C j : ℝ))
      ∧ (y j = 0 →
            (∑ r, (A j r : ℝ) * ν r * Real.exp (-∑ i, y i * (A i r : ℝ))) ≤ (C j : ℝ)) := by sorry

end KellyStochasticNetworks
