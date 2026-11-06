-- Prove2me | Theorems.Thm_GuthMaynard_kerr_double_sum_mono
-- name    : GuthMaynard.kerr_double_sum_mono
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T21:59:12.549883+00:00
-- url     : https://prove2.me/theorems/50aa9e95-2e06-401a-869b-aa82d14d91f1
-- title:
--   Kerr, Corollary 21 — S(N) ≪ M^ε S(M) for M ≥ 64N (all pairs)
-- statement:
--   For $\varepsilon > 0$ there is $C > 0$ such that for every finite set $A \subset \mathbb R$ and all integers $N \ge 1$, $M \ge 64N$,
--   $$S_A(N) \le C\,M^{\varepsilon}\,S_A(M), \qquad S_A(N) = \sum_{x,y\in A}\Big|\sum_{N\le n\le 2N} n^{-1/2}\,n^{i(x-y)}\Big|^2 .$$
--
--   This is the case $\gamma = 1_A$, with all pairs (no restriction $|t_r - t_s| \le \Delta$), of Corollary 21 of B. Kerr, *Large values of Dirichlet polynomials and zero density estimates for the Riemann zeta function*, arXiv:1909.12075v1 (2019), https://arxiv.org/abs/1909.12075, p. 19: “For any integer $M \geqslant 2N$ we have $$S(N, \Delta, \gamma) \ll M^{o(1)}S(M, \Delta, \gamma).$$”
--
--   **Formalization note.** The statement asks $M \ge 64N$ rather than $M \ge 2N$, and $A$ need not be separated. In this package it is a step of the reduction of Guth–Maynard's Theorem 1.6 (`GuthMaynard.heath_brown_large_values`) to `GuthMaynard.norm_dyadic_sum_cpow_le_dual_sum`.
-- source:
--   Kerr, B., Large values of Dirichlet polynomials and zero density estimates for the Riemann zeta function, arXiv:1909.12075v1 (2019), https://arxiv.org/abs/1909.12075, p. 19, Corollary 21 (case of an indicator weight, all pairs), a step of the reduction of Guth–Maynard Theorem 1.6 (Heath-Brown) (arXiv:2405.20552v2, p. 4)

import Mathlib

namespace GuthMaynard

theorem kerr_double_sum_mono : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℝ) (N M : ℕ), 1 ≤ N →
    64 * N ≤ M →
    (∑ x ∈ A, ∑ y ∈ A, ‖∑ n ∈ Finset.Icc N (2 * N), (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (n : ℂ) ^ (((x - y : ℝ) : ℂ) * Complex.I)‖ ^ 2) ≤
      C * (M : ℝ) ^ ε * (∑ x ∈ A, ∑ y ∈ A, ‖∑ n ∈ Finset.Icc M (2 * M), (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (n : ℂ) ^ (((x - y : ℝ) : ℂ) * Complex.I)‖ ^ 2) := by
  sorry

end GuthMaynard
