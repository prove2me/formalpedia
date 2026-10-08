-- Prove2me | Theorems.Thm_ManneLP_Equilibrium_table2_optimal_solution
-- name    : ManneLP.Equilibrium.table2_optimal_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:12:57.752461+00:00
-- url     : https://prove2.me/theorems/6539346b-90ac-42a6-8fb1-5aa8bb69dc22
-- title:
--   §6, Table 2 and footnote 3 — x₀₁ = 1/3, x₁₁ = 2/9, x₂₀ = 4/9 is optimal with cost 31/9; the do-nothing solution x₀₀ = 1 costs 4
-- statement:
--   In the numerical example of §6, let $x^*$ be given by
--   $$
--   x^*_{01}=\tfrac13,\qquad x^*_{11}=\tfrac29,\qquad x^*_{20}=\tfrac49,
--   $$
--   and $x^*_{ij}=0$ for every other admissible pair. Then:
--
--   1. $x^*$ is an optimal solution of the example's linear program (non-negativity, (4), (8.1)–(8.3); objective (9)), and its objective value is $\tfrac13\cdot5+\tfrac29\cdot4+\tfrac49\cdot2=\tfrac{31}{9}$;
--   2. its decoded decision rule $q(j\mid i)=x^*_{ij}/\sum_jx^*_{ij}$ orders one unit when the initial stock is $0$ or $1$ and nothing when it is $2$: $q(0\mid0)=0$, $q(1\mid0)=1$, $q(0\mid1)=0$, $q(1\mid1)=1$, $q(0\mid2)=1$, $q(1\mid2)=0$;
--   3. the do-nothing solution $x_{00}=1$ (all other unknowns $0$) is feasible, with objective value $4$.
--
--   The example shows the decoding of §3 at work: the optimal solution is a pure rule although mixed rules were admitted.
--
--   **Formalization Note** Table 2 writes $x_{30}=\varepsilon$, a small positive quantity, only "to eliminate the question of degeneracy"; the solution has $x_{30}=0$, and stock level $3$ is never visited, so no claim is made about the rule there. Uniqueness of the optimum is not claimed (the page does not claim it).
-- source:
--   Manne, Linear Programming and Sequential Decisions, Management Science 6 (1960), pp. 263–264 (PDF pp. 6–7), §6, Table 2, text on p. 264 and footnote 3

import Mathlib
import Definitions.Def_ManneLP_Equilibrium_Model
import Definitions.Def_ManneLP_Equilibrium_LP
import Definitions.Def_ManneLP_Equilibrium_Example

namespace ManneLP.Equilibrium

theorem table2_optimal_solution :
    IsLPOptimal exampleModel exampleOptimal ∧ lpObj exampleModel exampleOptimal = 31 / 9 ∧
    (decodeRule exampleModel exampleOptimal 0 0 = 0 ∧ decodeRule exampleModel exampleOptimal 0 1 = 1 ∧
      decodeRule exampleModel exampleOptimal 1 0 = 0 ∧ decodeRule exampleModel exampleOptimal 1 1 = 1 ∧
      decodeRule exampleModel exampleOptimal 2 0 = 1 ∧ decodeRule exampleModel exampleOptimal 2 1 = 0) ∧
    IsLPFeasible exampleModel exampleDoNothing ∧ lpObj exampleModel exampleDoNothing = 4 := by sorry

end ManneLP.Equilibrium
