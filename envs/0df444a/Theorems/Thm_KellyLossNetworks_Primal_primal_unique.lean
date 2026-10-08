-- Prove2me | Theorems.Thm_KellyLossNetworks_Primal_primal_unique
-- name    : KellyLossNetworks.Primal.primal_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:06:27.374934+00:00
-- url     : https://prove2.me/theorems/6d205dba-3a76-4449-a749-062977a715ff
-- title:
--   The primal problem has a unique optimum
-- statement:
--   Let $A_{jr}$ be nonnegative integers, $C_j$ nonnegative integer capacities, and $\nu_r>0$ for every route. On the feasible set $x\ge0$, $Ax\le C$, the objective
--
--   $$F(x)=\sum_r(x_r\log\nu_r-x_r\log x_r+x_r)$$
--
--   attains its maximum at exactly one flow vector $x$. This establishes the well-posed primal target used in Theorem 2.8.
--
--   **Formalization Note** The printed differentiability claim at $x_r=0$ is excluded; $x_r\log x_r$ takes its continuous value zero there.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 327, §2.1, paragraph after (2.1)

import Mathlib
import Definitions.Def_KellyLossNetworks_Primal_Problem

namespace KellyLossNetworks.Primal

/-- Kelly, *Loss networks* (1991), §2.1, p. 327, paragraph after (2.1).
Formalization Note: differentiability at zero is omitted because the printed assertion there is false. -/
theorem primal_unique {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r) :
    ∃! x : Fin R → ℝ,
      x ∈ primalFeasible A C ∧
      IsMaxOn (primalObjective ν) (primalFeasible A C) x := by sorry

end KellyLossNetworks.Primal
