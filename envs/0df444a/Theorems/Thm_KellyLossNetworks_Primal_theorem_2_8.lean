-- Prove2me | Theorems.Thm_KellyLossNetworks_Primal_theorem_2_8
-- name    : KellyLossNetworks.Primal.theorem_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:07:41.832673+00:00
-- url     : https://prove2.me/theorems/9e9b3bfe-3ea8-42b2-963c-d985594de936
-- title:
--   Theorem 2.8 — primal optimum and the blocking-dual bijection
-- statement:
--   Let $A_{jr}\in\mathbb N$ describe a finite loss network with offered traffic $\nu_r>0$ and link capacities $C_j\ge1$. The primal problem has exactly one optimum $x$. Every solution $B$ of conditions (2.7) describes that optimum by
--
--   $$x_r=\nu_r\prod_j(1-B_j)^{A_{jr}}.$$
--
--   A solution $B$ always exists, and it is unique if the real matrix $A$ has rank $J$, the number of links. Solutions $B$ are in bijection with optima $y$ of the dual problem: $B_j=1-e^{-y_j}$ and $y_j=-\log(1-B_j)$. Both directions and both inverse identities are asserted.
--
--   This theorem unifies the primal flow, link blocking, and convex dual formulations.
--
--   **Formalization Note** The feasible set includes both $x\ge0$ and $Ax\le C$. Positivity of $\nu$ makes $\log\nu_r$ meaningful; $C_j\ge1$ secures dual attainment and $B_j<1$. At $x_r=0$, $x_r\log x_r$ is the continuous value zero.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 329, Theorem 2.8

import Mathlib
import Definitions.Def_KellyLossNetworks_Primal_Problem

namespace KellyLossNetworks.Primal

/-- Kelly, *Loss networks*, Ann. Appl. Probab. 1(3) (1991), p. 329, Theorem 2.8.
Formalization Note: the positivity of offered traffic makes `log ν` meaningful; positive
capacities ensure dual attainment and that all blocking probabilities are below one. -/
theorem theorem_2_8 {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r)
    (hC : ∀ j, 1 ≤ C j) :
    (∃! x : Fin R → ℝ,
      x ∈ primalFeasible A C ∧
      IsMaxOn (primalObjective ν) (primalFeasible A C) x) ∧
    (∀ B : Fin J → ℝ, ConditionsOnB A ν C B →
      ∀ x : Fin R → ℝ,
        (x ∈ primalFeasible A C ∧
          IsMaxOn (primalObjective ν) (primalFeasible A C) x) →
        ∀ r, x r = ν r * ∏ j, (1 - B j) ^ (A j r)) ∧
    (∃ B : Fin J → ℝ, ConditionsOnB A ν C B) ∧
    ((Matrix.of fun j r => (A j r : ℝ)).rank = J →
      ∃! B : Fin J → ℝ, ConditionsOnB A ν C B) ∧
    (∀ B : Fin J → ℝ, ConditionsOnB A ν C B →
      IsDualOpt A ν C (dualFromBlocking B)) ∧
    (∀ y : Fin J → ℝ, IsDualOpt A ν C y →
      ConditionsOnB A ν C (blockingFromDual y)) ∧
    (∀ B : Fin J → ℝ, ConditionsOnB A ν C B →
      blockingFromDual (dualFromBlocking B) = B) ∧
    (∀ y : Fin J → ℝ, IsDualOpt A ν C y →
      dualFromBlocking (blockingFromDual y) = y) := by sorry

end KellyLossNetworks.Primal
