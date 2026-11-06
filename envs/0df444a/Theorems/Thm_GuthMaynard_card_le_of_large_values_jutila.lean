-- Prove2me | Theorems.Thm_GuthMaynard_card_le_of_large_values_jutila
-- name    : GuthMaynard.card_le_of_large_values_jutila
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T19:16:06.050557+00:00
-- url     : https://prove2.me/theorems/5c3ee0e0-a9d0-4e0f-b891-930081c39d15
-- title:
--   Jutila's large values estimate (Jutila 1977, Theorem (1.4))
-- statement:
--   For every $\varepsilon > 0$ and every integer $k \ge 1$ there is a constant $C$ such that for every $T \ge 2$, every integer $N \ge 1$, all complex $(a_n)$, every $V > 0$, and all $s_1, \dots, s_R \in \mathbb C$ with $\operatorname{Re}s_r \ge 0$, $|\operatorname{Im}s_r - \operatorname{Im}s_q| \le T$, and $|\operatorname{Im}s_r - \operatorname{Im}s_q| \ge 1$ for $r \ne q$: if $\big|\sum_{N < n \le 2N} a_nn^{-s_r}\big| \ge V$ for every $r$, then
--   $$R \le C\Big(GNV^{-2} + TG^{3-1/k}N^{1-1/k}V^{-6+2/k} + T(G^4N^2V^{-8})^k\Big)T^{\varepsilon}, \qquad G = \sum_{N<n\le 2N}|a_n|^2.$$
--
--   **Formalization note.** Stated from Jutila's Theorem, case (iii) (the principal character mod $1$, i.e. $\zeta$), for every fixed $k$. GM applies it with $k = 3$, $|b_n| \le 1$ (so $G \le N$), real points and $V = N^\sigma$.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 47, Jutila's large values estimate, cited in the proof of Proposition 12.1, which cites Jutila, M., Zero-density estimates for L-functions, Acta Arith. 32 (1977) 55–62, Theorem, (1.4), https://doi.org/10.4064/aa-32-1-55-62

import Mathlib

namespace GuthMaynard

theorem card_le_of_large_values_jutila (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → ∀ (N : ℕ), 1 ≤ N → ∀ (a : ℕ → ℂ) (V : ℝ), 0 < V →
      ∀ (R : ℕ) (s : Fin R → ℂ), (∀ r, 0 ≤ (s r).re) → (∀ r q, |(s r).im - (s q).im| ≤ T) →
      (∀ r q, r ≠ q → 1 ≤ |(s r).im - (s q).im|) →
      (∀ r, V ≤ ‖∑ n ∈ Finset.Ioc N (2 * N), a n * (n : ℂ) ^ (-s r)‖) →
      let G : ℝ := ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2
      (R : ℝ) ≤ C * (G * N / V ^ 2 +
        T * G ^ (3 - 1 / (k : ℝ)) * (N : ℝ) ^ (1 - 1 / (k : ℝ)) * V ^ (-6 + 2 / (k : ℝ)) +
        T * (G ^ 4 * (N : ℝ) ^ 2 / V ^ 8) ^ k) * T ^ ε := by
  sorry

end GuthMaynard
