-- Prove2me | Theorems.Thm_ManneJobShop_Formulation_relaxation_admits_overlap
-- name    : ManneJobShop.Formulation.relaxation_admits_overlap
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:58:42.240989+00:00
-- url     : https://prove2.me/theorems/0a07df65-a5e2-46d3-88ce-9364d5728a19
-- title:
--   p. 222 — the y_jk must be discrete: with real 0 ≤ y_jk ≤ 1, (3)–(4) admit x_j = x_k although (1) fails
-- statement:
--   Let $T$, $a_j$, $a_k$, $x$ be real numbers with $0<a_j\le T$ and $0<a_k\le T$, and let both tasks start on the same day, $x_j=x_k=x$. Then
--
--   1. there is a **real** $y_{jk}$ with
--   $$0\le y_{jk}\le 1,\qquad (T+a_k)\,y_{jk}+(x_j-x_k)\ge a_k,\qquad (T+a_j)(1-y_{jk})+(x_k-x_j)\ge a_j;$$
--   2. the either-or condition (1), $x_j-x_k\ge a_k$ or $x_k-x_j\ge a_j$, fails.
--
--   Hence if the integrality of $y_{jk}$ in (2) is dropped, conditions (3)–(4) no longer impose (1): this is why the $y_{jk}$ "are necessarily of a discrete nature".
--
--   **Formalization Note** The paper only says that $T$ is a "(large)" integer; the explicit reading here is $a_j,a_k\le T$, together with positive durations. The statement is the one-sided version; a fractional $y_{jk}$ exists at $x_j=x_k$ exactly when $a_ja_k\le T^2$, which is not stated.
-- source:
--   Manne, On the Job-Shop Scheduling Problem, Operations Research 8 (1960), p. 222, "The y_jk unknowns here are necessarily of a discrete nature. [Otherwise, it would be impossible to impose condition (1)]"

import Mathlib

namespace ManneJobShop.Formulation

/-- Manne (1960), p. 222: the `y_jk` must be discrete. With `y_jk` relaxed to a real number in
`[0, 1]`, and positive durations not exceeding `T`, conditions (3) and (4) can be met with
`x_j = x_k = x`, although the either-or condition (1) fails there. -/
theorem relaxation_admits_overlap (T aj ak x : ℝ) (haj : 0 < aj) (hak : 0 < ak)
    (hajT : aj ≤ T) (hakT : ak ≤ T) :
    (∃ y : ℝ, (0 ≤ y ∧ y ≤ 1) ∧
        (T + ak) * y + (x - x) ≥ ak ∧ (T + aj) * (1 - y) + (x - x) ≥ aj) ∧
      ¬ (x - x ≥ ak ∨ x - x ≥ aj) := by sorry

end ManneJobShop.Formulation
