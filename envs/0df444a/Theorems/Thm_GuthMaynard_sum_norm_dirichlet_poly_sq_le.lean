-- Prove2me | Theorems.Thm_GuthMaynard_sum_norm_dirichlet_poly_sq_le
-- name    : GuthMaynard.sum_norm_dirichlet_poly_sq_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T21:22:12.9463+00:00
-- url     : https://prove2.me/theorems/36ee9e96-d6f3-44c6-a050-f2674cc9d587
-- title:
--   Hölder + Heath-Brown bound for short Dirichlet polynomials over pairs (Guth–Maynard (6.2)–(6.3))
-- statement:
--   Let $k \ge 1$. For every $\delta > 0$ there are $C$ and $T_0$ such that for all $T \ge T_0$, every finite set $W$ contained in an interval $[a, a+T]$ whose distinct points are at distance at least $1$, every integer $1 \le M \le T^2$, and all complex $(c_m)$ with $|c_m| \le 1$,
--   $$\sum_{t_1, t_2 \in W}\Big|\sum_{1 \le m \le M} c_m m^{i(t_1 - t_2)}\Big|^2 \le C\,T^{\delta}\Big(|W|^2M + M^2|W|^{2-1/k} + |W|^{2-3/(4k)}T^{1/(2k)}M\Big).$$
--
--   This is the step of the proof of Guth–Maynard's Proposition 6.1 that combines (6.2) and (6.3) (pp. 18–19, arXiv:2405.20552v2). It applies Hölder's inequality with exponent $k$, writes the $k$-th power as a Dirichlet polynomial of length $M^k$ whose coefficients the divisor bound controls, and applies Heath-Brown's Theorem 1.6 (`GuthMaynard.heath_brown_large_values`) to its dyadic blocks. It is published separately so that the proof of Proposition 6.1 (`GuthMaynard.norm_S_two_le`) fits the verifier's time limit. Unlike the paper, the inner sum runs over all of $1 \le m \le M$ rather than one dyadic block $m \sim M$.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), pp. 18–19, (6.2)–(6.3) in the proof of Proposition 6.1 (a step of that proof)

import Mathlib
import Definitions.Def_GuthMaynard

namespace GuthMaynard

theorem sum_norm_dirichlet_poly_sq_le (k : ℕ) (hk : 1 ≤ k) : ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    ∀ (W : Finset ℝ) (a : ℝ), IsSeparated 1 W → (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
    ∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ T ^ 2 → ∀ c : ℕ → ℂ, (∀ m, ‖c m‖ ≤ 1) →
      ∑ t₁ ∈ W, ∑ t₂ ∈ W,
          ‖∑ m ∈ Finset.Icc 1 M, c m * (m : ℂ) ^ (((t₁ - t₂ : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
        C * T ^ δ * ((W.card : ℝ) ^ 2 * M + (M : ℝ) ^ 2 * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
          (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ))) * M) := by
  sorry

end GuthMaynard
