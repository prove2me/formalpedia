-- Prove2me | Theorems.Thm_LinearOptimization_network_integer_optimum_exists
-- name    : LinearOptimization.network_integer_optimum_exists
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T22:00:19.000114+00:00
-- url     : https://prove2.me/theorems/272bef19-41c4-49a8-a345-80a85be985a3
-- title:
--   Existence of integer optimal flows and integer dual optima
-- statement:
--   **(Bertsimas & Tsitsiklis, Corollary 7.2, p. 290)** Consider an uncapacitated network flow problem, and assume that the optimal cost is finite.
--
--   - **(a)** If all supplies $b_i$ are integer, there exists an integer optimal flow vector.
--   - **(b)** If all cost coefficients $c_{ij}$ are integer, there exists an integer optimal solution to the dual problem.
--
--   (Stated in §7.3 under standing Assumption 7.1: $\sum_{i\in\mathcal{N}}b_i=0$ and the graph connected. The dual problem is the LP dual of the standard-form problem $\min \mathbf{c}'\mathbf{f}$ s.t. $\tilde{\mathbf{A}}\mathbf{f}=\tilde{\mathbf{b}}$, $\mathbf{f}\ge 0$.)
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Corollary 7.2, p. 290

import Definitions.Def_LinearOptimization_NetworkFlowProblem
import Definitions.Def_Polyhedron
import Definitions.Def_LinearOptimization_DualLP


open Matrix

/-- **Bertsimas & Tsitsiklis, Corollary 7.2 (p. 290).** For the uncapacitated network flow
problem `min c'f, Ãf = b̃, f ≥ 0` on a connected graph with `∑ᵢ bᵢ = 0`
and finite optimal cost: integer supplies yield an integer optimal flow
vector, and integer costs yield an integer optimal solution of the dual
`max p'b̃, p'Ã ≤ c'`. -/

theorem LinearOptimization.network_integer_optimum_exists {n m : ℕ}
    (arcs : Fin m → Fin (n + 1) × Fin (n + 1)) (bsupply : Fin (n + 1) → ℝ)
    (cost : Fin m → ℝ)
    (hloop : HasNoSelfLoops arcs) (hconn : IsConnectedNetwork arcs)
    (hsum : ∑ i, bsupply i = 0)
    (hfin :
      lpValue cost
          (stdPolyhedron (truncatedIncidence arcs) (truncatedSupply bsupply)) ≠ ⊤ ∧
      lpValue cost
          (stdPolyhedron (truncatedIncidence arcs) (truncatedSupply bsupply)) ≠ ⊥) :
    ((∀ i, ∃ z : ℤ, bsupply i = (z : ℝ)) →
      ∃ f, IsLpOptimal cost
          (stdPolyhedron (truncatedIncidence arcs) (truncatedSupply bsupply)) f ∧
        ∀ k, ∃ z : ℤ, f k = (z : ℝ)) ∧
    ((∀ k, ∃ z : ℤ, cost k = (z : ℝ)) →
      ∃ p, IsLpDualOptimal (truncatedSupply bsupply)
          (dualFeasibleStd (truncatedIncidence arcs) cost) p ∧
        ∀ i, ∃ z : ℤ, p i = (z : ℝ)) := by
  sorry
