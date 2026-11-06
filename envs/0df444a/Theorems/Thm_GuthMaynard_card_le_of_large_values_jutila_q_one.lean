-- Prove2me | Theorems.Thm_GuthMaynard_card_le_of_large_values_jutila_q_one
-- name    : GuthMaynard.card_le_of_large_values_jutila_q_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T21:41:29.34207+00:00
-- url     : https://prove2.me/theorems/a801c45b-1d29-438d-a5d4-3c7ed0058e4d
-- title:
--   Jutila 1977, Theorem (1.2) at q = 1 — large values of Dirichlet polynomials
-- statement:
--   For every $\varepsilon > 0$ and every integer $k \ge 1$ there is a constant $C$ such that for every $T \ge 2$, every integer $N \ge 1$, all complex $(a_n)$, every $V > 0$, and all $s_1, \dots, s_R \in \mathbb C$ with $\operatorname{Re}s_r \ge 0$, $|\operatorname{Im}s_r - \operatorname{Im}s_q| \le T$, and $|\operatorname{Im}s_r - \operatorname{Im}s_q| \ge 1$ for $r \ne q$: if $\big|\sum_{N < n \le 2N} a_nn^{-s_r}\big| \ge V$ for every $r$, then
--   $$R \le C\Big(GNV^{-2} + T(G^4N^2V^{-8})^k + (TG^2V^{-4})^k\Big)T^{\varepsilon}, \qquad G = \sum_{N<n\le 2N}|a_n|^2.$$
--
--   This is case (i) of the Theorem of M. Jutila, *Zero-density estimates for $L$-functions*, Acta Arith. 32 (1977) 55–62, https://doi.org/10.4064/aa-32-1-55-62, p. 56, with modulus $q = 1$: “**THEOREM.** Let $\varepsilon$ be any fixed positive number and $k$ any fixed positive integer. Then in the notation above (with $T \geqslant 2$), we have $$R_1 \ll_{\varepsilon,k}\big(GNV^{-2} + qT(G^4N^2V^{-8})^k + (qTG^2V^{-4})^k\big)(qT)^\varepsilon, \qquad (1.2)$$” where $f(s,\chi) = \sum_{N+1}^{2N}a_n\chi(n)n^{-s}$, $G = \sum_{N+1}^{2N}|a_n|^2$, the points satisfy $\sigma_r \ge 0$ and $|t_r - t_s| \le T$, and “for $r \ne s$ either $\chi_r \ne \chi_s$ or $|t_r - t_s| \ge 1$” (p. 55), with $|f(s_r,\chi_r)| \ge V > 0$, and $R_1$ counts the pairs when all $\chi_r$ belong to the same modulus $q$. For $q = 1$ the only character is $\chi_0 \bmod 1$, so the pairs are just the points $s_r$, $1$-separated in height. Jutila proves (1.2) on pp. 58–60 from the Halász–Montgomery inequality, Lemma 1 (a transformation of the smoothed kernel through the functional equation) and Lemma 3 (a mean value estimate resting on the fourth power moment (2.4)).
--
--   **Formalization note.** Only the case $q = 1$ is stated. Jutila (p. 60) derives (1.4), Guth–Maynard's citation [Ju, Theorem (1.4)] (arXiv:2405.20552v2, p. 47), from this case: “for the proof of (1.4), we use (1.2) and the Huxley subdivision of the points $s_r$. It means we apply (1.2) with $q = 1$, $T = T_0$ and multiply the resulting estimate by $1 + T_0^{-1}T$; an optimal choice of $T_0$ completes the proof.” In this package it is the input of a reduction of `GuthMaynard.card_le_of_large_values_jutila`.
-- source:
--   Jutila, M., Zero-density estimates for L-functions, Acta Arith. 32 (1977) 55–62, https://doi.org/10.4064/aa-32-1-55-62, p. 56, Theorem, (1.2) with q = 1, used for Guth–Maynard p. 47 via Jutila (1.4), p. 60

import Mathlib

namespace GuthMaynard

theorem card_le_of_large_values_jutila_q_one (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → ∀ (N : ℕ), 1 ≤ N → ∀ (a : ℕ → ℂ) (V : ℝ), 0 < V →
      ∀ (R : ℕ) (s : Fin R → ℂ), (∀ r, 0 ≤ (s r).re) → (∀ r q, |(s r).im - (s q).im| ≤ T) →
      (∀ r q, r ≠ q → 1 ≤ |(s r).im - (s q).im|) →
      (∀ r, V ≤ ‖∑ n ∈ Finset.Ioc N (2 * N), a n * (n : ℂ) ^ (-s r)‖) →
      let G : ℝ := ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2
      (R : ℝ) ≤ C * (G * N / V ^ 2 + T * (G ^ 4 * (N : ℝ) ^ 2 / V ^ 8) ^ k +
        (T * G ^ 2 / V ^ 4) ^ k) * T ^ ε := by
  sorry

end GuthMaynard
