-- Prove2me | Theorems.Thm_ManneJobShop_Formulation_pair_either_or_iff
-- name    : ManneJobShop.Formulation.pair_either_or_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:58:25.987365+00:00
-- url     : https://prove2.me/theorems/0849585c-7415-4b07-b5d1-f44ee2c6d806
-- title:
--   p. 220, conditions (1)–(4) — given |x_j − x_k| ≤ T, some y_jk ∈ {0, 1} satisfies (3) and (4) iff (1) holds
-- statement:
--   Let $T$, $a_j$, $a_k$, $x_j$, $x_k$ be integers with $|x_j-x_k|\le T$. Then there is an integer $y_{jk}$ with
--   $$0\le y_{jk}\le 1,\qquad (T+a_k)\,y_{jk}+(x_j-x_k)\ge a_k,\qquad (T+a_j)(1-y_{jk})+(x_k-x_j)\ge a_j$$
--   (Manne's conditions (2), (3), (4)) if and only if the either-or condition (1) holds:
--   $$x_j-x_k\ge a_k\quad\text{or}\quad x_k-x_j\ge a_j .$$
--
--   This is the correctness of Manne's linearization of the nonconvex noninterference condition (1) for one pair of tasks on the same machine: the 0–1 variable $y_{jk}$ records which job goes first, and the coefficients $T+a_k$, $T+a_j$ switch the inactive inequality off.
--
--   **Formalization Note** The paper writes "We already know that $|x_j-x_k|\le T$", which follows from $0\le x_j,x_k\le T$; here it is a hypothesis. No sign condition on $a_j,a_k$ is needed. The paper's summary table of admissible values of $y_{jk}$ is not stated row by row (for $0<x_j-x_k<a_k$ condition (3) in fact forces $y_{jk}=1$); its content is this equivalence together with the exclusion of $x_j=x_k$ (a separate statement).
-- source:
--   Manne, On the Job-Shop Scheduling Problem, Operations Research 8 (1960), p. 220, conditions (1)–(4), "Condition (2) ensures that y_jk equals either zero or else unity" … "Equations (3) and (4) then ensure"

import Mathlib

namespace ManneJobShop.Formulation

/-- Manne (1960), p. 220, conditions (1)–(4): when `|x_j - x_k| ≤ T`, some integer `y_jk` with
`0 ≤ y_jk ≤ 1` satisfies (3) and (4) iff the either-or condition (1) holds. -/
theorem pair_either_or_iff (T aj ak xj xk : ℤ) (hT : |xj - xk| ≤ T) :
    (∃ y : ℤ, (0 ≤ y ∧ y ≤ 1) ∧
        (T + ak) * y + (xj - xk) ≥ ak ∧ (T + aj) * (1 - y) + (xk - xj) ≥ aj) ↔
      (xj - xk ≥ ak ∨ xk - xj ≥ aj) := by sorry

end ManneJobShop.Formulation
