-- Prove2me | Theorems.Thm_GuthMaynard_card_le_of_large_values
-- name    : GuthMaynard.card_le_of_large_values
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T19:17:48.955361+00:00
-- url     : https://prove2.me/theorems/60ec1d12-461f-408f-9d9b-ff3d0d3fa3bf
-- title:
--   Theorem 1.1 (Large values estimate)
-- statement:
--   Guth–Maynard, p. 1: “**Theorem 1.1** (Large values estimate)**.** *Suppose $(b_n)$ is a sequence of complex numbers with $|b_n| \le 1$, and $(t_r)_{r\le R}$ is a sequence of $1$-separated points in $[0,T]$ such that* $$\Big|\sum_{n=N}^{2N} b_n n^{it_r}\Big| \ge V$$ *for all $r \le R$. Then we have* $$R \le T^{o(1)}\Big(N^2V^{-2} + N^{18/5}V^{-4} + TN^{12/5}V^{-4}\Big).$$”
--
--   For every $\varepsilon > 0$ there is $T_0$ such that for all $T \ge T_0$, all integers $N \ge 1$, all $V > 0$, all complex $(b_n)_{n \ge 0}$ with $|b_n| \le 1$, and all $t_0, \dots, t_{R-1} \in [0, T]$ with $|t_r - t_s| \ge 1$ for $r \ne s$: if $\big|\sum_{N \le n \le 2N} b_n n^{it_r}\big| \ge V$ for every $r$, then
--   $$R \le T^{\varepsilon}\Big(\frac{N^2}{V^2} + \frac{N^{18/5}}{V^4} + \frac{T N^{12/5}}{V^4}\Big).$$
--
--   **Formalization note.** The factor $T^{o(1)}$ is read with §1.2's convention ("Asymptotic quantities such as $o(1)$ are interpreted as $T \to \infty$", p. 5), uniformly in $N$, $V$, $(b_n)$ and $(t_r)$: for each $\varepsilon > 0$ the bound with $T^{\varepsilon}$ holds once $T$ is large. "1-separated" is read as distance at least $1$. The paper leaves implicit that $N \ge 1$ is an integer and $V > 0$, and both are assumed here. The sum runs over $N \le n \le 2N$, exactly as printed.
--
--   The form with the weaker $\ell^2$ constraint $\sum_{N \le n \le 2N}|b_n|^2 \le KN$ in place of $|b_n| \le 1$, which the paper says it does not know how to obtain (p. 5), is the separate Open statement [`GuthMaynard.card_le_of_large_values_of_sum_sq_le`](https://prove2.me/theorems/be58ac81-b4f9-45c2-bb2f-7865f3b20b33).
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 1, Theorem 1.1 (Large values estimate)

import Mathlib

namespace GuthMaynard

theorem card_le_of_large_values :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∀ (N : ℕ), 1 ≤ N → ∀ (V : ℝ), 0 < V → ∀ (b : ℕ → ℂ), (∀ n, ‖b n‖ ≤ 1) →
      ∀ (R : ℕ) (t : Fin R → ℝ), (∀ r s, r ≠ s → 1 ≤ |t r - t s|) → (∀ r, t r ∈ Set.Icc 0 T) →
      (∀ r, V ≤ ‖∑ n ∈ Finset.Icc N (2 * N), b n * (n : ℂ) ^ ((t r : ℂ) * Complex.I)‖) →
      (R : ℝ) ≤ T ^ ε * ((N : ℝ) ^ 2 / V ^ 2 + (N : ℝ) ^ (18 / 5 : ℝ) / V ^ 4 +
        T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ 4) := by
  sorry

end GuthMaynard
