-- Prove2me | Theorems.Thm_MulticutLShaped_SimpleRecourse_relaxation_stop
-- name    : MulticutLShaped.SimpleRecourse.relaxation_stop
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:23:39.887152+00:00
-- url     : https://prove2.me/theorems/47bf2be4-5e09-426f-b75e-9508aae99830
-- title:
--   Section 5, p. 389 — (26) relaxes (25), and the stopping rule yields an optimum of (25)
-- statement:
--   Let $I$ be any set of pairs $(i,j)$ identified in Step 2 of the multicut algorithm for simple recourse problems, and let (26) be the master program with identified pairs $I$:
--   $$
--   \min\ cx+\sum_{i,j}p_{ij}q^-_{ij}(T_ix)+\sum_{l\in I}u_l\quad\text{s.t. } Ax=b,\ x\ge0,\ u_l\ge e_l-E_lx,\ u_l\ge0\ (l\in I),
--   $$
--   with $E_l=p_{ij}q_{ij}T_i$, $e_l=p_{ij}q_{ij}h_{ij}$ for $l=(i,j)$.
--
--   1. **Relaxation.** If $(x,\chi,u)$ is feasible for (25), then $(x,u)$ is feasible for (26), and
--   $$
--   \Big(cx+\sum_{i,j}p_{ij}q^-_{ij}(T_ix)+\sum_{l\in I}u_l\Big)-\sum_{i,j}p_{ij}q^-_{ij}h_{ij}\ \le\ \text{(25)-objective of }(x,\chi,u).
--   $$
--   2. **Stopping.** If $(x,u)$ is optimal for (26) and the constraint (27), $0\ge p_{ij}q_{ij}(h_{ij}-T_ix)$, is violated by no pair $(i,j)\notin I$, then $(x,Tx,\tilde u)$ is optimal for (25), where $\tilde u_l=u_l$ for $l\in I$ and $\tilde u_l=0$ for $l\notin I$.
--
--   Part 1 is the paper's remark that the constraints of (26) are a subset of those of (25); part 2 is why the algorithm may stop when (27) identifies no new constraint.
--
--   **Formalization Note.** The constant $-\sum_{i,j}p_{ij}q^-_{ij}h_{ij}$, which the paper drops from the objective of (26), is restored in part 1. The constraint $x\ge0$ is kept in both programs.
-- source:
--   Birge and Louveaux, A multicut algorithm for two-stage stochastic linear programs, Eur. J. Oper. Res. 34 (1988), p. 389, Section 5, remark after Step 2 of the multicut algorithm for simple recourse problems

import Mathlib
import Definitions.Def_MulticutLShaped_SimpleRecourse_Algorithm

namespace MulticutLShaped.SimpleRecourse

variable {n1 m1 m2 J : ℕ}

/-- p. 389: the constraints of (26) are a subset of those of (25), and the algorithm's stopping
rule is correct. For every set `I` of identified pairs:
1. every `(x, χ, u)` feasible for (25) gives a feasible `(x, u)` for (26) whose objective, after
   the constant `−Σ_i Σ_j p_ij q⁻_ij h_ij` dropped from (26) is restored, is at most the (25)
   objective;
2. if `(x, u)` is optimal for (26) and (27) is violated by no unidentified pair at `x`, then
   `(x, Tx, ũ)` is optimal for (25), where `ũ_l = u_l` for `l ∈ I` and `ũ_l = 0` otherwise. -/
theorem relaxation_stop (inst : Instance n1 m1 m2 J) (I : Finset (Fin m2 × Fin J)) :
    (∀ x χ u, Feasible25 inst x χ u →
      MasterFeasible inst I x (fun l => u l.1 l.2) ∧
      masterObj inst I x (fun l => u l.1 l.2) -
          ∑ i, ∑ j, inst.p i j * inst.qminus i j * inst.h i j ≤ obj25 inst x χ u) ∧
    ∀ x u, MasterOptimal inst I x u → violated inst I x = ∅ →
      IsOptimal25 inst x (inst.T.mulVec x) (fun i j => if (i, j) ∈ I then u (i, j) else 0) := by sorry

end MulticutLShaped.SimpleRecourse
