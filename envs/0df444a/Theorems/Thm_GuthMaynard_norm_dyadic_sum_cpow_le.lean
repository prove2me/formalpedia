-- Prove2me | Theorems.Thm_GuthMaynard_norm_dyadic_sum_cpow_le
-- name    : GuthMaynard.norm_dyadic_sum_cpow_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T21:59:13.671107+00:00
-- url     : https://prove2.me/theorems/9d96ce2c-f835-4335-8f2a-79393bf5a425
-- title:
--   |∑_{N≤n≤2N} n^{iu}| ≪ N/|u| + |u|^{1/2} log(|u|+2) for |u| ≥ 1
-- statement:
--   There is $C > 0$ such that for every integer $N \ge 1$ and every real $u$ with $|u| \ge 1$,
--   $$\Big|\sum_{N\le n\le 2N} n^{iu}\Big| \le C\Big(\frac{N}{|u|} + |u|^{1/2}\log(|u|+2)\Big).$$
--
--   This is the estimate used in the proof of Lemma 24 of B. Kerr, *Large values of Dirichlet polynomials and zero density estimates for the Riemann zeta function*, arXiv:1909.12075v1 (2019), https://arxiv.org/abs/1909.12075, p. 22: “For $S_2$ we use the estimate $$\sum_{N\leqslant n\leqslant 2N} n^{it} \ll \frac{N}{t} + t^{1/2}(\log t),$$ valid for any $N, t \geqslant 1$, see for example [11, Equation 9.21]” ([11] is Iwaniec–Kowalski, *Analytic Number Theory*, AMS 2004).
--
--   **Formalization note.** The statement takes $|u| \ge 1$ of either sign and $\log(|u|+2)$ in place of $\log t$, which vanishes at $t = 1$. In this package it is a step of the reduction of Guth–Maynard's Theorem 1.6 (`GuthMaynard.heath_brown_large_values`).
-- source:
--   Kerr, B., Large values of Dirichlet polynomials and zero density estimates for the Riemann zeta function, arXiv:1909.12075v1 (2019), https://arxiv.org/abs/1909.12075, p. 22, the estimate in the proof of Lemma 24, a step of the reduction of Guth–Maynard Theorem 1.6 (Heath-Brown) (arXiv:2405.20552v2, p. 4)

import Mathlib

namespace GuthMaynard

theorem norm_dyadic_sum_cpow_le : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ u : ℝ, 1 ≤ |u| →
    ‖∑ n ∈ Finset.Icc N (2 * N), (n : ℂ) ^ ((u : ℂ) * Complex.I)‖ ≤
      C * (N / |u| + |u| ^ (1 / 2 : ℝ) * Real.log (|u| + 2)) := by
  sorry

end GuthMaynard
