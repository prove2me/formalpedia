-- Prove2me | Theorems.Thm_GuthMaynard_energy_le_of_large_values_of_three_quarters
-- name    : GuthMaynard.energy_le_of_large_values_of_three_quarters
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T19:15:12.628135+00:00
-- url     : https://prove2.me/theorems/1fc2236c-e5c0-44a9-ba5d-23d1b1c4f6d6
-- title:
--   Proposition 11.1 (Bound for energy)
-- statement:
--   For every $\delta > 0$ there are $C$ and $T_0$ such that for all $T \ge T_0$, every integer $N$ with $T^{3/4} \le N \le T$, every real $\sigma$, all complex $(b_n)$ with $|b_n| \le 1$, and every finite set $W$ contained in an interval $[a, a+T]$ whose distinct points are at distance at least $1$: if $\big|\sum_{N < n \le 2N} b_n n^{it}\big| \ge N^\sigma$ for all $t \in W$, then
--   $$E(W) \le C\,T^{\delta}\Big(|W|N^{4-4\sigma} + |W|^{21/8}T^{1/4}N^{1-2\sigma} + |W|^3N^{1-2\sigma}\Big),$$
--   where $E(W)$ is the number of $(w_1, w_2, w_3, w_4) \in W^4$ with $|w_1 + w_2 - w_3 - w_4| \le 1$ (`energy W`).
--
--   **Formalization note.** $n \sim N$ is $N < n \le 2N$ (§1.2), and $\lessapprox$ is §1.2's convention.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 38, Proposition 11.1 (Bound for energy)

import Mathlib
import Definitions.Def_GuthMaynard

namespace GuthMaynard

theorem energy_le_of_large_values_of_three_quarters :
    ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ),
      (N : ℝ) ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T → ∀ (σ : ℝ) (b : ℕ → ℂ), (∀ n, ‖b n‖ ≤ 1) →
      ∀ (W : Finset ℝ) (a : ℝ), IsSeparated 1 W → (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
      (∀ t ∈ W, (N : ℝ) ^ σ ≤
        ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖) →
      (energy W : ℝ) ≤ C * T ^ δ * ((W.card : ℝ) * (N : ℝ) ^ (4 - 4 * σ) +
        (W.card : ℝ) ^ (21 / 8 : ℝ) * T ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 - 2 * σ) +
        (W.card : ℝ) ^ 3 * (N : ℝ) ^ (1 - 2 * σ)) := by
  sorry

end GuthMaynard
