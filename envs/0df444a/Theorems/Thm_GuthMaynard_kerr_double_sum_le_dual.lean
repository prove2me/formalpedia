-- Prove2me | Theorems.Thm_GuthMaynard_kerr_double_sum_le_dual
-- name    : GuthMaynard.kerr_double_sum_le_dual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T21:59:27.536237+00:00
-- url     : https://prove2.me/theorems/3d3cdea2-dd20-4bb6-a5f3-147efe3fb039
-- title:
--   Kerr, Corollary 28 — S(N) ≪ T^ε (S(M) + |A|² + N|A|) for M ≥ 64(T/N + 1) (all pairs)
-- statement:
--   For $\varepsilon > 0$ there is $C > 0$ such that for every finite $1$-separated set $A \subset \mathbb R$ of diameter at most $T$, with $T \ge 2$, and all integers $1 \le N \le T$ and $M$ with $64(T/N + 1) \le M \le 200T^2$,
--   $$S_A(N) \le C\,T^{\varepsilon}\big(S_A(M) + |A|^2 + N|A|\big), \qquad S_A(N) = \sum_{x,y\in A}\Big|\sum_{N\le n\le 2N} n^{-1/2}\,n^{i(x-y)}\Big|^2 .$$
--
--   This is the case $\gamma = 1_A$, $\Delta = T$ (all pairs), of Corollary 28 of B. Kerr, *Large values of Dirichlet polynomials and zero density estimates for the Riemann zeta function*, arXiv:1909.12075v1 (2019), https://arxiv.org/abs/1909.12075, p. 25: “Let $T$ be a real number, $1 \leqslant t_1, \dots, t_R \leqslant T$ a well spaced sequence and $\gamma(t)$ a sequence of positive real numbers. We have $$S(N, \Delta, \gamma) \ll N^{o(1)}S\Big(\frac{4\Delta}{N}, \Delta, \gamma\Big) + N^{o(1)}I(\Delta, \gamma) + \|\gamma\|_2N^{1+o(1)}.$$”
--
--   **Formalization note.** The dual length is any integer $M$ between $64(T/N+1)$ and $200T^2$ (Kerr: $4\Delta/N$), the losses are $T^{\varepsilon}$, and the last term is $N|A| = N\|\gamma\|_2^2$. Kerr's proof rests on Lemma 26, published here as `GuthMaynard.norm_dyadic_sum_cpow_le_dual_sum`. In this package it is a step of the reduction of Guth–Maynard's Theorem 1.6 (`GuthMaynard.heath_brown_large_values`).
-- source:
--   Kerr, B., Large values of Dirichlet polynomials and zero density estimates for the Riemann zeta function, arXiv:1909.12075v1 (2019), https://arxiv.org/abs/1909.12075, p. 25, Corollary 28 (case of an indicator weight, all pairs), a step of the reduction of Guth–Maynard Theorem 1.6 (Heath-Brown) (arXiv:2405.20552v2, p. 4)

import Mathlib
import Definitions.Def_GuthMaynard

namespace GuthMaynard

theorem kerr_double_sum_le_dual : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℝ) (T : ℝ) (N M : ℕ),
    IsSeparated 1 A → (∀ x ∈ A, ∀ y ∈ A, |x - y| ≤ T) → 2 ≤ T → 1 ≤ N → (N : ℝ) ≤ T →
    64 * (T / N + 1) ≤ M → (M : ℝ) ≤ 200 * T ^ 2 →
    (∑ x ∈ A, ∑ y ∈ A, ‖∑ n ∈ Finset.Icc N (2 * N), (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (n : ℂ) ^ (((x - y : ℝ) : ℂ) * Complex.I)‖ ^ 2) ≤
      C * T ^ ε * ((∑ x ∈ A, ∑ y ∈ A, ‖∑ n ∈ Finset.Icc M (2 * M), (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (n : ℂ) ^ (((x - y : ℝ) : ℂ) * Complex.I)‖ ^ 2) + (A.card : ℝ) ^ 2 + N * A.card) := by
  sorry

end GuthMaynard
