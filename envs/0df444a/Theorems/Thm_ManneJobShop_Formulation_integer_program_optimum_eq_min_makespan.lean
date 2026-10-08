-- Prove2me | Theorems.Thm_ManneJobShop_Formulation_integer_program_optimum_eq_min_makespan
-- name    : ManneJobShop.Formulation.integer_program_optimum_eq_min_makespan
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:09:24.05641+00:00
-- url     : https://prove2.me/theorems/a13bb893-e062-4b79-916a-141a230b398a
-- title:
--   p. 221, formulation (2)–(7) — the least t of Manne's integer program is the minimum make-span of the job shop
-- statement:
--   Fix a job-shop instance with $n\ge1$ tasks: machines $\mu(j)$, integer durations $a_j$, horizon $T$, precedence pairs, exact delays $\Theta_{jk}$ and delivery dates. Let $\mathcal S$ be the set of schedules, i.e. integer start days $x\in\{0,\dots,T\}^n$ satisfying the either-or condition (1) on every pair of tasks on the same machine, precedence (5a), exact delays (5c) and delivery dates (6), and let $\operatorname{ms}(x)=\max_j(x_j+a_j)$ be the make-span. Then for every integer $t^\ast$,
--   $$t^\ast=\min\bigl\{\,t\in\mathbb Z:\ \exists\,x,\,y \text{ integer satisfying } 0\le x_j\le T,\ (2)\text{–}(7)\,\bigr\}\iff t^\ast=\min_{x\in\mathcal S}\operatorname{ms}(x),$$
--   where each side asserts that the minimum exists and equals $t^\ast$.
--
--   This is the content of Manne's formulation: minimizing $t$ over his integer program with one 0–1 variable per conflicting pair solves the make-span problem of the job shop exactly. In particular the integer program has an optimum if and only if a schedule exists.
--
--   **Formalization Note** "Minimization of $t$" is read as `IsLeast` on both sides. On the schedule side the make-span is the maximum `Finset.sup'` of $x_j+a_j$, not "the least $t$ with (7)", so the equivalence is not definitional. Both problems use the horizon $0\le x_j\le T$ of p. 219; redundancy of $T$ is not assumed. $n\ge1$ is supplied as `[NeZero n]`: with no tasks every integer $t$ is feasible and the program has no least $t$. Durations are arbitrary integers.
-- source:
--   Manne, On the Job-Shop Scheduling Problem, Operations Research 8 (1960), p. 221, formulation (2)–(7), "If this calendar time is denoted by t, the problem now consists of the minimization of t …"; p. 219, the make-span

import Mathlib
import Definitions.Def_ManneJobShop_Formulation_Model

namespace ManneJobShop.Formulation

/-- Manne (1960), p. 221, formulation (2)–(7): for an instance with at least one task, an integer
`t₀` is the least `t` for which the integer program (2)–(7) is solvable iff `t₀` is the least
make-span `max_j (x_j + a_j)` over all schedules. -/
theorem integer_program_optimum_eq_min_makespan {n : ℕ} [NeZero n] (I : Instance n) (t₀ : ℤ) :
    IsLeast {t : ℤ | ∃ x y, IsIPFeasible I x y t} t₀ ↔
      IsLeast (makespan I '' {x | IsSchedule I x}) t₀ := by sorry

end ManneJobShop.Formulation
