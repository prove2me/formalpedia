-- Prove2me | Theorems.Thm_GilmoreGomory61_CuttingStock_step4_current_solution_is_minimum
-- name    : GilmoreGomory61.CuttingStock.step4_current_solution_is_minimum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:10:40.649793+00:00
-- url     : https://prove2.me/theorems/c0c77aa4-7ec0-4153-a2d2-0dbc6d0a3425
-- title:
--   pp. 854–855, step (4) — no profitable column makes the basic cutting solution optimal
-- statement:
--   Let $B$ be the bordered matrix of a feasible cutting-stock basis, $\bar N=B^{-1}N'$, and $b_i$ the noninitial entries in the first row of $B^{-1}$. Suppose every nonbasic surplus column has $b_i\ge0$, and no stock length $L_j$ of cost $c_j$ admits a nonnegative integer cutting pattern with
--
--   $$
--   \sum_i\ell_i a_i\le L_j,\qquad \sum_i b_i a_i>c_j.
--   $$
--
--   Then the current basic solution satisfies all demand equations, has cost equal to the first entry of $\bar N$, and is a minimum of the real cutting-stock linear program: every feasible solution using any finitely many activities and surplus columns has cost at least that value.
--
--   This is the stopping test of routine step (4). It certifies optimality against the full activity set, even though the current tableau contains only $m$ basic columns.
--
--   **Formalization Note** The paper's one-based $(i+1)$st bordered row is Lean's demand coordinate $i$. Only nonbasic surplus columns are tested. The theorem needs neither positive piece lengths nor nondegeneracy; its conclusion compares with every feasible finitely supported solution.
-- source:
--   Gilmore and Gomory, A linear programming approach to the cutting-stock problem, Oper. Res. 9(6) (1961), pp. 854–855, step (4)

import Mathlib
import Definitions.Def_GilmoreGomory61_CuttingStock_Basis

namespace GilmoreGomory61.CuttingStock

/-- Routine step (4): no improving surplus or cutting pattern makes the current basis globally optimal. -/
theorem step4_current_solution_is_minimum {m k : ℕ} (I : Instance m k)
    (β : Fin m → Col I) (hβ : IsFeasibleBasis I β)
    (h3 : ∀ i, Sum.inr i ∉ Set.range β → 0 ≤ mult I β i)
    (h4 : ∀ j : Fin k, ¬ ∃ a : Fin m → ℕ,
      patLen I a ≤ I.L j ∧ I.c j < ∑ i, mult I β i * (a i : ℝ)) :
    Feasible I (basicSol I β) ∧
    cost I (basicSol I β) = Nbar I β (Sum.inl ()) ∧
    ∀ z : Col I →₀ ℝ, Feasible I z → Nbar I β (Sum.inl ()) ≤ cost I z := by sorry

end GilmoreGomory61.CuttingStock
