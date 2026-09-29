-- Prove2me | Theorems.Thm_Irrational_exists_int_linear_forms_tendsto_zero
-- name    : Irrational.exists_int_linear_forms_tendsto_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-10T21:22:22.166964+00:00
-- url     : https://prove2.me/theorems/65fc14b7-7835-4496-9730-999c0db3254d
-- title:
--   Every irrational number admits vanishing integer linear forms
-- statement:
--   Let $x$ be an irrational real number. Then there are integer sequences $(p_n)$ and $(q_n)$ with $q_n > 0$ such that the linear forms
--
--   $$L_n \;=\; q_n x - p_n$$
--
--   are all non-zero and satisfy $L_n \to 0$.
--
--   This is the converse of the classical irrationality criterion, and it follows from Dirichlet's approximation theorem: for each $n \ge 1$ there are integers $j$ and $k$ with $0 < k \le n$ and
--
--   $$|k x - j| \;\le\; \frac{1}{n+1},$$
--
--   and irrationality of $x$ forbids $kx - j = 0$. Together with the criterion it shows that, for any real number, the existence of non-vanishing integer linear forms tending to zero is *equivalent* to irrationality — so a search for such forms is a complete strategy, never a lossy one.
-- source:
--   Classical; converse to the standard irrationality criterion, obtained from Dirichlet's approximation theorem (Mathlib: `Real.exists_int_int_abs_mul_sub_le`).

import Mathlib

theorem Irrational.exists_int_linear_forms_tendsto_zero {x : ℝ} (hx : Irrational x) :
    ∃ p q : ℕ → ℤ, (∀ n, 0 < q n) ∧
      (∀ n, (q n : ℝ) * x - (p n : ℝ) ≠ 0) ∧
      Filter.Tendsto (fun n => (q n : ℝ) * x - (p n : ℝ)) Filter.atTop (nhds 0) := by sorry
