-- Prove2me | Theorems.Thm_HetImpatient_FluidSplit_proposition_1
-- name    : HetImpatient.FluidSplit.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:54.623984+00:00
-- url     : https://prove2.me/theorems/2870bcf4-48da-4379-9baa-f20ee13ebd78
-- title:
--   Proposition 1, p. 1071 — the fluid-optimal multi-class schedule uses at most m + 1 subclasses and splits at most one class, into two
-- statement:
--   Consider the fluid model with $m$ classes, class $i$ having arrival rate $\Lambda_i > 0$, service rate $\mu_i > 0$, patience survival function $\bar F_i$ (values in $[0,1]$, nonincreasing, $\bar F_i(\infty) = 0$) and per-customer cost $\bar c_i(w)$ at offered wait $w\in[0,\infty]$, and a total capacity $N$. A feasible plan for the program (2) with $C_i$ defined in (6) consists of capacities $n_i \ge 0$ with $\sum_i n_i \le N$ and, for each class $i$, a split into $J(i)\ge 1$ FCFS subclasses with rates $\lambda_{i,j}\ge 0$, offered waits $w_{i,j}$ and capacities $n_{i,j}\ge 0$ satisfying
--   $$\sum_{j=1}^{J(i)} \lambda_{i,j} = \Lambda_i,\qquad \lambda_{i,j}\,\bar F_i(w_{i,j}) \le n_{i,j}\,\mu_i,\qquad \sum_{j=1}^{J(i)} n_{i,j} \le n_i ;$$
--   its cost is $\sum_i \sum_j \lambda_{i,j}\,\bar c_i(w_{i,j})$.
--
--   **Statement.** Every feasible plan is weakly improved by a feasible plan $Q$ (possibly with different capacities $n_i$) such that
--
--   1. $Q$ uses at most $m+1$ subclasses in total: $\sum_{i=1}^m J(i) \le m+1$;
--   2. $J(i) > 1$ for at most one class $i$;
--   3. for that class, $J(i) = 2$.
--
--   In particular, whenever the fluid program has an optimal solution, it has one that splits the $m$ classes into at most $m+1$ subclasses, splitting at most one class, and that one into exactly two.
--
--   This is the paper's Proposition 1. Although Lemma 1 allows each class to be split in two on its own, at the joint optimum only one class needs to be differentiated; the optimal policy differentiates among customers of at most one class.
--
--   **Formalization Note.** "The fluid-optimal solution … splits the $m$ customer classes into at most $m+1$ subclasses" is stated in reduction form: every feasible plan is weakly improved by a feasible plan with the stated structure. Applied to an optimal plan it gives an optimal plan with that structure, which is the paper's statement, and the reduction does not depend on optima existing (the paper does not show attainment). It does not claim that every optimal plan has the structure, which fails when costs tie (the paper notes optima can be multiple, p. 1071). The improved plan may reallocate capacity across classes; only the total budget $\sum_i n_i \le N$ is shared. Offered waits range over $[0,\infty]$; the cost $\bar c_i$ is an arbitrary real function of the offered wait (any such function arises from (5)).
-- source:
--   Bassamboo, Randhawa & Wu, Optimally scheduling heterogeneous impatient customers, Manufacturing & Service Operations Management 25(3):1066–1080 (2023), p. 1071, Proposition 1

import Mathlib
import Definitions.Def_HetImpatient_FluidSplit_Model

namespace HetImpatient.FluidSplit

theorem proposition_1 {m : ℕ} (D : ClassData m) (hD : D.Standing) (N : ℝ)
    (P : Plan m) (hP : PlanFeasible D N P) :
    ∃ Q : Plan m, PlanFeasible D N Q ∧ planCost D Q ≤ planCost D P ∧
      ∑ i, (Q.cfg i).J ≤ m + 1 ∧
      (∀ i k, 1 < (Q.cfg i).J → 1 < (Q.cfg k).J → i = k) ∧
      (∀ i, 1 < (Q.cfg i).J → (Q.cfg i).J = 2) := by sorry

end HetImpatient.FluidSplit
