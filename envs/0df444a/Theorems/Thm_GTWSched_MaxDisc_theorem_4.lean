-- Prove2me | Theorems.Thm_GTWSched_MaxDisc_theorem_4
-- name    : GTWSched.MaxDisc.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:48:43.377979+00:00
-- url     : https://prove2.me/theorems/4eec9309-0675-49ab-949f-ab887fa269e0
-- title:
--   THEOREM 4, pp. 342–343 — some optimum schedule has the release time property w.r.t. a maximum-deadline task
-- statement:
--   Let $N$ tasks on one processor have lengths $l_i \ge 0$, release times $r_i \ge 0$ and deadlines $d_i$ in special form for a constant $\alpha \ge 0$: for every $i$, either $d_i - r_i = l_i + \alpha$, or $r_i = 0$ and $d_i < l_i + \alpha$. Let $T_n$ be a task with the largest deadline, $d_i \le d_n$ for all $i$. If a feasible schedule exists, then there is an optimum schedule (feasible, of minimum makespan among all feasible schedules) such that
--
--   $$\text{every task } T_i \text{ executed after } T_n \text{ has } r_i > s_n,$$
--
--   where $s_n$ is the starting time of $T_n$; that is, the schedule has the release time property.
--
--   This is the key normalization result of §3.1; Corollaries 1 and 2 and the paper's algorithm for the maximum-discrepancy problem rest on it. For arbitrary release times and deadlines it is false: the special form is essential.
--
--   **Formalization Note.** Schedules are an execution order (a permutation of the task indices) plus starting times; "executed after" refers to that order. Tasks are indexed by `Fin N`.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), pp. 342–343, THEOREM 4

import Mathlib
import Definitions.Def_GTWSched_MaxDisc_Model

namespace GTWSched.MaxDisc

theorem theorem_4 {N : ℕ} (r d l : Fin N → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hr : ∀ i, 0 ≤ r i) (hl : ∀ i, 0 ≤ l i) (hsf : SpecialForm r d l α)
    (n : Fin N) (hn : ∀ i, d i ≤ d n)
    (hfeas : ∃ (σ : Fin N ≃ Fin N) (s : Fin N → ℝ), Feasible r d l σ s) :
    ∃ (σ : Fin N ≃ Fin N) (s : Fin N → ℝ),
      Optimum r d l σ s ∧ ReleaseTimeProperty r σ s n := by sorry

end GTWSched.MaxDisc
