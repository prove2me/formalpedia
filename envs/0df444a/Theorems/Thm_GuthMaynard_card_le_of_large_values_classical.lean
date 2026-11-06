-- Prove2me | Theorems.Thm_GuthMaynard_card_le_of_large_values_classical
-- name    : GuthMaynard.card_le_of_large_values_classical
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T18:13:27.64871+00:00
-- url     : https://prove2.me/theorems/b2b213b9-3af2-4000-a24c-5bbb8fc43875
-- title:
--   (1.1) — the classical large values bound
-- statement:
--   For every $\varepsilon > 0$ there is $T_0$ such that for all $T \ge T_0$, all integers $N \ge 1$, all $V > 0$, all complex $(b_n)$ with $|b_n| \le 1$, and all $t_0, \dots, t_{R-1} \in [0, T]$ with $|t_r - t_s| \ge 1$ for $r \ne s$: if $\big|\sum_{N \le n \le 2N} b_n n^{it_r}\big| \ge V$ for every $r$, then
--   $$R \le T^{\varepsilon}\Big(\frac{N^2}{V^2} + T\min\Big(\frac{N}{V^2}, \frac{N^4}{V^6}\Big)\Big).$$
--
--   **Formalization note.** The hypotheses are those of Theorem 1.1, to which the display is compared, and $T^{o(1)}$ is read as there.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 1, (1.1)

import Mathlib

namespace GuthMaynard

theorem card_le_of_large_values_classical :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∀ (N : ℕ), 1 ≤ N → ∀ (V : ℝ), 0 < V → ∀ (b : ℕ → ℂ), (∀ n, ‖b n‖ ≤ 1) →
      ∀ (R : ℕ) (t : Fin R → ℝ), (∀ r s, r ≠ s → 1 ≤ |t r - t s|) → (∀ r, t r ∈ Set.Icc 0 T) →
      (∀ r, V ≤ ‖∑ n ∈ Finset.Icc N (2 * N), b n * (n : ℂ) ^ ((t r : ℂ) * Complex.I)‖) →
      (R : ℝ) ≤ T ^ ε * ((N : ℝ) ^ 2 / V ^ 2 + T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6)) := by
  sorry

end GuthMaynard
