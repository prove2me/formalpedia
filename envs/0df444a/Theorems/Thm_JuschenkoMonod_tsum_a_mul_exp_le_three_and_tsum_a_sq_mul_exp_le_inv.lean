-- Prove2me | Theorems.Thm_JuschenkoMonod_tsum_a_mul_exp_le_three_and_tsum_a_sq_mul_exp_le_inv
-- name    : JuschenkoMonod.tsum_a_mul_exp_le_three_and_tsum_a_sq_mul_exp_le_inv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:21:52.467655+00:00
-- url     : https://prove2.me/theorems/3e347f36-e897-4a40-b12c-4609827c6644
-- title:
--   Lemma 2.4 — ∑ a_{n,j} e^{−|j|/n} ≤ 3 and ∑ a_{n,j}² e^{−2|j|/n} ≤ 1/n
-- statement:
--   Let $n \ge 1$ be an integer and $a_{n,j} = \exp(-ne^{-|j|/n})$ for $j \in \mathbf Z$. Then:
--   - the series $\sum_{j\in\mathbf Z} a_{n,j}e^{-|j|/n}$ converges, and its sum is at most $3$;
--   - the series $\sum_{j\in\mathbf Z} a_{n,j}^2e^{-2|j|/n}$ converges, and its sum is at most $1/n$.
--
--   *Formalization note.* "For all $n$" is read as all integers $n \ge 1$, since $a_{n,j}$ and $e^{-|j|/n}$ divide by $n$. That both series converge is stated explicitly.
-- source:
--   Juschenko, K. and Monod, N., Cantor systems, piecewise translations and simple amenable groups, Ann. of Math. (2) 178 (2013) 775–787, https://doi.org/10.4007/annals.2013.178.2.7, p. 779, Lemma 2.4

import Mathlib
import Definitions.Def_JuschenkoMonod

namespace JuschenkoMonod

theorem tsum_a_mul_exp_le_three_and_tsum_a_sq_mul_exp_le_inv (n : ℕ) (hn : 0 < n) :
    (Summable fun j : ℤ => a n j * Real.exp (-(|j| : ℝ) / n)) ∧
      ∑' j : ℤ, a n j * Real.exp (-(|j| : ℝ) / n) ≤ 3 ∧
      (Summable fun j : ℤ => a n j ^ 2 * Real.exp (-2 * (|j| : ℝ) / n)) ∧
      ∑' j : ℤ, a n j ^ 2 * Real.exp (-2 * (|j| : ℝ) / n) ≤ 1 / n := by
  sorry

end JuschenkoMonod
