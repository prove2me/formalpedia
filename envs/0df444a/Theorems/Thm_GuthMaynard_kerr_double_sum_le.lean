-- Prove2me | Theorems.Thm_GuthMaynard_kerr_double_sum_le
-- name    : GuthMaynard.kerr_double_sum_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T21:59:22.924876+00:00
-- url     : https://prove2.me/theorems/f93eb8c7-d25a-444b-8df0-3a420fce9ef9
-- title:
--   Kerr, Theorem 16 — S(N) ≪ T^ε (|A|² + N|A| + T^{1/2}|A|^{5/4}) for well-spaced A (all pairs)
-- statement:
--   For $\varepsilon > 0$ there is $C > 0$ such that for every finite $1$-separated set $A \subset \mathbb R$ of diameter at most $T$, with $T \ge 2$, and every integer $N \ge 1$,
--   $$S_A(N) \le C\,T^{\varepsilon}\big(|A|^2 + N|A| + T^{1/2}|A|^{5/4}\big), \qquad S_A(N) = \sum_{x,y\in A}\Big|\sum_{N\le n\le 2N} n^{-1/2}\,n^{i(x-y)}\Big|^2 .$$
--
--   This is the case $\gamma = 1_A$, $\Delta = T$, of Theorem 16 of B. Kerr, *Large values of Dirichlet polynomials and zero density estimates for the Riemann zeta function*, arXiv:1909.12075v1 (2019), https://arxiv.org/abs/1909.12075, p. 13: “… and in general $$S(N, \Delta, \gamma) \ll (I(\Delta, \gamma) + N\|\gamma\|_2^2 + \Delta^{1/2}I(\Delta, \gamma)^{1/4}\|\gamma\|_2^{3/2})N^{o(1)}.$$” For $\gamma = 1_A$, $I(T, \gamma) = |A|^2$ and $\|\gamma\|_2^2 = |A|$. It is Heath-Brown's Theorem 1 (J. London Math. Soc. (2) 20 (1979)) in the form Kerr states, which Guth–Maynard quote as their Theorem 1.6.
--
--   **Formalization note.** The loss is $T^{\varepsilon}$ for every $N \ge 1$; for $N > T$ the mean value theorem gives it. Kerr's display (26) defines $S$ without the weight $n^{-1/2}$, while the proofs on pp. 14–26 use it; the statement here has the weight. In this package it is the last step of the reduction of `GuthMaynard.heath_brown_large_values` to `GuthMaynard.norm_dyadic_sum_cpow_le_dual_sum`.
-- source:
--   Kerr, B., Large values of Dirichlet polynomials and zero density estimates for the Riemann zeta function, arXiv:1909.12075v1 (2019), https://arxiv.org/abs/1909.12075, p. 13, Theorem 16 (case of an indicator weight, all pairs), a step of the reduction of Guth–Maynard Theorem 1.6 (Heath-Brown) (arXiv:2405.20552v2, p. 4)

import Mathlib
import Definitions.Def_GuthMaynard

namespace GuthMaynard

theorem kerr_double_sum_le : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℝ) (T : ℝ) (N : ℕ),
    IsSeparated 1 A → (∀ x ∈ A, ∀ y ∈ A, |x - y| ≤ T) → 2 ≤ T → 1 ≤ N →
    (∑ x ∈ A, ∑ y ∈ A, ‖∑ n ∈ Finset.Icc N (2 * N), (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (n : ℂ) ^ (((x - y : ℝ) : ℂ) * Complex.I)‖ ^ 2) ≤
      C * T ^ ε * ((A.card : ℝ) ^ 2 + N * A.card + T ^ (1 / 2 : ℝ) * (A.card : ℝ) ^ (5 / 4 : ℝ)) := by
  sorry

end GuthMaynard
