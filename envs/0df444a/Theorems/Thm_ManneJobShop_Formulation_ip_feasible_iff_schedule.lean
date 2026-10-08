-- Prove2me | Theorems.Thm_ManneJobShop_Formulation_ip_feasible_iff_schedule
-- name    : ManneJobShop.Formulation.ip_feasible_iff_schedule
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:09:23.839299+00:00
-- url     : https://prove2.me/theorems/83f53f15-8d46-4403-acab-a627e099efad
-- title:
--   pp. 220–221, constraints (2)–(7) — for fixed x and t, some y solves (2)–(7) iff x is a schedule with x_j + a_j ≤ t for all j
-- statement:
--   Fix a job-shop instance (tasks, machines, integer durations $a_j$, horizon $T$, precedence pairs, exact delays $\Theta_{jk}$ and delivery dates), integer start days $x=(x_1,\dots,x_n)$ and an integer $t$. Then there are integers $y_{jk}$, one for each conflicting pair, such that $(x,y,t)$ satisfies Manne's integer program — $0\le x_j\le T$, (2), (3), (4) on every conflicting pair, (5a), (5c), (6) and (7) — if and only if $x$ is a schedule (start days in $\{0,\dots,T\}$ satisfying the either-or condition (1) on every conflicting pair, (5a), (5c) and (6)) and
--   $$x_j+a_j\le t\qquad\text{for every task } j .$$
--
--   This is the feasibility half of Manne's claim that the problem "now consists of the minimization of $t$" subject to (2)–(7): the integer program describes exactly the schedules, with $t$ an upper bound on every completion day.
--
--   **Formalization Note** The objects are those of the definitions file `ManneJobShop.Formulation.Model`. The statement holds for arbitrary integer durations, without positivity.
-- source:
--   Manne, On the Job-Shop Scheduling Problem, Operations Research 8 (1960), pp. 220–221, constraints (2)–(7), "If this calendar time is denoted by t, the problem now consists of the minimization of t …"

import Mathlib
import Definitions.Def_ManneJobShop_Formulation_Model

namespace ManneJobShop.Formulation

/-- Manne (1960), pp. 220–221: for fixed start days `x` and bound `t`, the integer program
(2)–(7) has a solution `y` iff `x` is a schedule (horizon, (1), (5a), (5c), (6)) satisfying (7). -/
theorem ip_feasible_iff_schedule {n : ℕ} (I : Instance n) (x : Fin n → ℤ) (t : ℤ) :
    (∃ y : Fin n → Fin n → ℤ, IsIPFeasible I x y t) ↔
      (IsSchedule I x ∧ ∀ j, x j + I.a j ≤ t) := by sorry

end ManneJobShop.Formulation
