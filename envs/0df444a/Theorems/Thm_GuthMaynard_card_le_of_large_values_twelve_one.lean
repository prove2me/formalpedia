-- Prove2me | Theorems.Thm_GuthMaynard_card_le_of_large_values_twelve_one
-- name    : GuthMaynard.card_le_of_large_values_twelve_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T00:37:05.81232+00:00
-- url     : https://prove2.me/theorems/3809ad02-24ab-4205-9242-7ea6d24bd7dd
-- title:
--   Guth–Maynard (12.1) — the eight-term large values bound for T^{5/6} ≤ N ≤ T, fixed k
-- statement:
--   For every integer $k \ge 1$ and every $\delta > 0$ there are $C$ and $T_0$ such that for all $T \ge T_0$, every integer $N$ with $T^{5/6} \le N \le T$, every real $\sigma$, all complex $(b_n)$ with $|b_n| \le 1$, and all $t_0, \dots, t_{R-1} \in [0, T]$ with $|t_r - t_s| \ge 1$ for $r \ne s$: if $\big|\sum_{N < n \le 2N} b_n n^{it_r}\big| \ge N^\sigma$ for every $r$, then
--   $$R \le C\,T^{\delta}\Big(N^{2-2\sigma} + N^{5-6\sigma} + T^{\frac{k}{k+1}}N^{(4-6\sigma)\frac{k}{k+1}} + N^{(5-6\sigma)\frac{4k}{4k+3}}T^{\frac{2}{4k+3}} + T^{4/3}N^{2-4\sigma} + T^{1/2}N^{3-4\sigma} + TN^{9/2-7\sigma} + T^{18/19}N^{72/19-112\sigma/19}\Big).$$
--
--   This is the bound (12.1) of Guth–Maynard (arXiv:2405.20552v2, p. 46), from the proof of their Proposition 3.1: “$|W| \lessapprox_{\epsilon,k} N^{2-2\sigma} + N^{5-6\sigma} + T^{\frac{k}{k+1}}N^{(4-6\sigma)\frac{k}{k+1}} + N^{(5-6\sigma)\frac{4k}{4k+3}}T^{\frac{2}{4k+3}} + T^{4/3}N^{2-4\sigma} + T^{1/2}N^{3-4\sigma} + TN^{9/2-7\sigma} + T^{18/19}N^{72/19-112\sigma/19}$.” There it is derived for a set $W$ of large values of the smoothed polynomial in an interval of length $T = N^{6/5}$; the proof of Proposition 12.1 (p. 47) uses it for every $T$ with $T^{5/6} \le N \le T$ and for the sharp sum, which is the form stated here.
--
--   **Formalization note.** In this package it is a step of the proof of Proposition 12.1 (`GuthMaynard.card_le_of_large_values_of_five_sixths`), published separately so that each proof piece fits the verifier's time limit. $\lessapprox_{\epsilon,k}$ is read as $\le C\,T^{\delta}$ with $C$ depending on $k$ and $\delta$.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 46, (12.1), in the form the proof of Proposition 12.1 (p. 47) applies it

import Mathlib

namespace GuthMaynard

theorem card_le_of_large_values_twelve_one (k : ℕ) (hk : 1 ≤ k) :
    ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ),
      (N : ℝ) ∈ Set.Icc (T ^ (5 / 6 : ℝ)) T → ∀ σ : ℝ, ∀ b : ℕ → ℂ,
      (∀ n, ‖b n‖ ≤ 1) → ∀ (R : ℕ) (t : Fin R → ℝ), (∀ r s, r ≠ s → 1 ≤ |t r - t s|) →
      (∀ r, t r ∈ Set.Icc 0 T) →
      (∀ r, (N : ℝ) ^ σ ≤
        ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t r : ℂ) * Complex.I)‖) →
      (R : ℝ) ≤ C * T ^ δ * ((N : ℝ) ^ (2 - 2 * σ) + (N : ℝ) ^ (5 - 6 * σ) +
        T ^ ((k : ℝ) / (k + 1)) * (N : ℝ) ^ ((4 - 6 * σ) * ((k : ℝ) / (k + 1))) +
        (N : ℝ) ^ ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) * T ^ (2 / (4 * (k : ℝ) + 3)) +
        T ^ (4 / 3 : ℝ) * (N : ℝ) ^ (2 - 4 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
        T * (N : ℝ) ^ (9 / 2 - 7 * σ) + T ^ (18 / 19 : ℝ) * (N : ℝ) ^ (72 / 19 - 112 * σ / 19)) := by
  sorry

end GuthMaynard
