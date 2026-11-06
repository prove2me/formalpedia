-- Prove2me | Theorems.Thm_GuthMaynard_heath_brown_large_values
-- name    : GuthMaynard.heath_brown_large_values
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T18:17:03.313323+00:00
-- url     : https://prove2.me/theorems/5eb858da-491c-4a44-b326-23e2c21f769b
-- title:
--   Theorem 1.6 (Heath-Brown)
-- statement:
--   For every $\varepsilon > 0$ there are $\delta > 0$ and $T_0$ such that for all $T \ge T_0$, every integer $N \ge 1$, all complex $(a_n)$ with $|a_n| \le T^{\delta}$, and every finite set $\mathcal T$ contained in an interval $[c, c+T]$ whose distinct points are at distance at least $1$,
--   $$\sum_{t_1, t_2 \in \mathcal T}\Big|\sum_{N \le n \le 2N} a_nn^{i(t_1-t_2)}\Big|^2 \le T^{\varepsilon}\Big(|\mathcal T|^2N + |\mathcal T|N^2 + |\mathcal T|^{5/4}T^{1/2}N\Big).$$
--
--   **Formalization note.** "$|a_n| \le T^{o(1)}$ … $\le T^{o(1)}(\dots)$" is read as: for every $\varepsilon > 0$ there is $\delta > 0$ such that coefficients bounded by $T^\delta$ give the bound with $T^\varepsilon$, for all large $T$, uniformly in $N$ and $\mathcal T$. The sum runs over $N \le n \le 2N$ as printed here (the §6 restatement, p. 19, writes $n \sim N$ and $|a_n| \lessapprox 1$).
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 4, Theorem 1.6 (Heath-Brown), which cites Heath-Brown, D. R., A large values estimate for Dirichlet polynomials, J. London Math. Soc. (2) 20 (1979) 8–18, https://doi.org/10.1112/jlms/s2-20.1.8

import Mathlib
import Definitions.Def_GuthMaynard

namespace GuthMaynard

theorem heath_brown_large_values :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ), 1 ≤ N →
      ∀ a : ℕ → ℂ, (∀ n, ‖a n‖ ≤ T ^ δ) → ∀ (P : Finset ℝ) (c : ℝ), IsSeparated 1 P →
      (∀ t ∈ P, t ∈ Set.Icc c (c + T)) →
      ∑ t₁ ∈ P, ∑ t₂ ∈ P, ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (((t₁ - t₂ : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
        T ^ ε * ((P.card : ℝ) ^ 2 * N + (P.card : ℝ) * (N : ℝ) ^ 2 +
          (P.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * N) := by
  sorry

end GuthMaynard
