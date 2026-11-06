-- Prove2me | Theorems.Thm_GuthMaynard_card_le_of_large_values_huxley
-- name    : GuthMaynard.card_le_of_large_values_huxley
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T18:13:44.588227+00:00
-- url     : https://prove2.me/theorems/3cdfeb2c-4a7e-4141-bca1-5f22396bd67b
-- title:
--   The Montgomery–Halász–Huxley large values estimate (Huxley 1972, (2.9))
-- statement:
--   There is an absolute constant $C$ such that for every integer $N \ge 1$, every $T \ge 2$, all complex $a(1), \dots, a(N)$, every $V > 0$, and all $s_1, \dots, s_R \in \mathbb C$ with $0 \le \operatorname{Re}s_r \le 1/4$ and $1 \le |\operatorname{Im}s_r - \operatorname{Im}s_q| \le T$ for $r \ne q$: if $\big|\sum_{m=1}^N a(m)m^{-s_r}\big| \ge V$ for every $r$, then
--   $$R \le C\Big(GNV^{-2} + G^3NTV^{-6}\log^2(NT)\Big), \qquad G = \sum_{m=1}^N |a(m)|^2.$$
--
--   **Formalization note.** Stated from Huxley's §2, in that paper's notation and with its hypotheses (2.1)–(2.4). GM's (1.1) uses it with $|a(m)| \le 1$ supported on $[N, 2N]$ (so $G \le 2N$), real points, and $\log^2(NT) = T^{o(1)}$. $T \ge 2$ is added so that the logarithm is positive; Huxley's $T$ is a large parameter.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 1, the Montgomery–Halász–Huxley large values estimate behind (1.1), which cites Huxley, M. N., On the difference between consecutive primes, Invent. Math. 15 (1972) 164–170, §2, (2.9), https://doi.org/10.1007/BF01418933

import Mathlib

namespace GuthMaynard

theorem card_le_of_large_values_huxley :
    ∃ C : ℝ, ∀ (N : ℕ), 1 ≤ N → ∀ T : ℝ, 2 ≤ T → ∀ (a : ℕ → ℂ) (V : ℝ), 0 < V →
      ∀ (R : ℕ) (s : Fin R → ℂ), (∀ r, 0 ≤ (s r).re ∧ (s r).re ≤ 1 / 4) →
      (∀ r q, r ≠ q → 1 ≤ |(s r).im - (s q).im| ∧ |(s r).im - (s q).im| ≤ T) →
      (∀ r, V ≤ ‖∑ m ∈ Finset.Icc 1 N, a m * (m : ℂ) ^ (-s r)‖) →
      (R : ℝ) ≤ C * ((∑ m ∈ Finset.Icc 1 N, ‖a m‖ ^ 2) * N / V ^ 2 +
        (∑ m ∈ Finset.Icc 1 N, ‖a m‖ ^ 2) ^ 3 * N * T / V ^ 6 * Real.log (N * T) ^ 2) := by
  sorry

end GuthMaynard
