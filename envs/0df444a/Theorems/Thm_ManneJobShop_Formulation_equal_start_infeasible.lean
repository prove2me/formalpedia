-- Prove2me | Theorems.Thm_ManneJobShop_Formulation_equal_start_infeasible
-- name    : ManneJobShop.Formulation.equal_start_infeasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:58:40.415294+00:00
-- url     : https://prove2.me/theorems/5f5c841b-35c2-4320-b069-2703d84abbf5
-- title:
--   p. 220, conditions (2)–(4) — if x_j = x_k and a_j, a_k > 0, no y_jk satisfies (2), (3) and (4)
-- statement:
--   Let $T$ and $x$ be integers and $a_j,a_k$ positive integers. If two tasks start on the same day, $x_j=x_k=x$, then there is no integer $y_{jk}$ with
--   $$0\le y_{jk}\le 1,\qquad (T+a_k)\,y_{jk}+(x_j-x_k)\ge a_k,\qquad (T+a_j)(1-y_{jk})+(x_k-x_j)\ge a_j .$$
--
--   So Manne's constraints (2)–(4) forbid two tasks on the same machine from starting on the same day, as the either-or condition (1) demands.
--
--   **Formalization Note** The positivity $a_j,a_k>0$ is the paper's setting (each task occupies the machine for a positive integral number of days) and is necessary: with $a_k=0$ the value $y_{jk}=0$ satisfies both inequalities when $x_j=x_k$. The common start day is the single variable $x$, so the differences $x_j-x_k$ and $x_k-x_j$ appear as $x-x$.
-- source:
--   Manne, On the Job-Shop Scheduling Problem, Operations Research 8 (1960), p. 220, conditions (2)–(4), "Hence if (x_j − x_k) = 0, there is no value that can be assigned to y_jk"

import Mathlib

namespace ManneJobShop.Formulation

/-- Manne (1960), p. 220: if `x_j = x_k` (both equal to `x`) and the durations are positive, no
integer `y_jk` with `0 ≤ y_jk ≤ 1` satisfies both (3) and (4). -/
theorem equal_start_infeasible (T aj ak x : ℤ) (haj : 0 < aj) (hak : 0 < ak) :
    ¬ ∃ y : ℤ, (0 ≤ y ∧ y ≤ 1) ∧
        (T + ak) * y + (x - x) ≥ ak ∧ (T + aj) * (1 - y) + (x - x) ≥ aj := by sorry

end ManneJobShop.Formulation
