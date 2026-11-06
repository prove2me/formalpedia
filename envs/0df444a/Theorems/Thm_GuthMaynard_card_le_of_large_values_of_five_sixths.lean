-- Prove2me | Theorems.Thm_GuthMaynard_card_le_of_large_values_of_five_sixths
-- name    : GuthMaynard.card_le_of_large_values_of_five_sixths
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T19:15:51.392148+00:00
-- url     : https://prove2.me/theorems/68ed747b-2069-4193-8a05-131c17dd7fbe
-- title:
--   Proposition 12.1 (Large values estimate for N ≥ T^{5/6})
-- statement:
--   For every $\delta > 0$ there are $C$ and $T_0$ such that for all $T \ge T_0$, every integer $N$ with $T^{5/6} \le N \le T$, every $\sigma \ge 7/10$, all complex $(b_n)$ with $|b_n| \le 1$, and all $t_0, \dots, t_{R-1} \in [0, T]$ with $|t_r - t_s| \ge 1$ for $r \ne s$: if $\big|\sum_{N < n \le 2N} b_n n^{it_r}\big| \ge N^\sigma$ for every $r$, then both
--   $$R \le C\,T^{\delta}\Big(N^{2-2\sigma} + T^{1/2}N^{3-4\sigma} + \inf_{k \ge 1}\Big(T^{\frac{k}{k+1}}N^{(4-6\sigma)\frac{k}{k+1}} + N^{(5-6\sigma)\frac{4k}{4k+3}}T^{\frac{2}{4k+3}}\Big)\Big)$$
--   and
--   $$R \le C\,T^{\delta}\Big(N^{2-2\sigma} + T^{1/2}N^{3-4\sigma} + T^{(30\sigma-21)/5}N^{(46-60\sigma)/5}\Big).$$
--
--   **Formalization note.** "As in Theorem 1.1" supplies $|b_n| \le 1$ and $1$-separated $t_r \in [0, T]$; the sum is over $n \sim N$, that is $N < n \le 2N$ (§1.2). $V = N^\sigma$. $\lessapprox$ is §1.2's convention. Both displays are one statement, as printed.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 47, Proposition 12.1 (Large values estimate for N ≥ T^{5/6})

import Mathlib

namespace GuthMaynard

theorem card_le_of_large_values_of_five_sixths :
    ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ),
      (N : ℝ) ∈ Set.Icc (T ^ (5 / 6 : ℝ)) T → ∀ σ : ℝ, 7 / 10 ≤ σ → ∀ b : ℕ → ℂ,
      (∀ n, ‖b n‖ ≤ 1) → ∀ (R : ℕ) (t : Fin R → ℝ), (∀ r s, r ≠ s → 1 ≤ |t r - t s|) →
      (∀ r, t r ∈ Set.Icc 0 T) →
      (∀ r, (N : ℝ) ^ σ ≤
        ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t r : ℂ) * Complex.I)‖) →
      (R : ℝ) ≤ C * T ^ δ * ((N : ℝ) ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
        ⨅ k : ℕ+, (T ^ ((k : ℝ) / (k + 1)) * (N : ℝ) ^ ((4 - 6 * σ) * ((k : ℝ) / (k + 1))) +
          (N : ℝ) ^ ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) * T ^ (2 / (4 * (k : ℝ) + 3)))) ∧
      (R : ℝ) ≤ C * T ^ δ * ((N : ℝ) ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
        T ^ ((30 * σ - 21) / 5) * (N : ℝ) ^ ((46 - 60 * σ) / 5)) := by
  sorry

end GuthMaynard
