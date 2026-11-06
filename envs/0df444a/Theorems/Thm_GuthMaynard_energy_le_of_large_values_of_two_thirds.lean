-- Prove2me | Theorems.Thm_GuthMaynard_energy_le_of_large_values_of_two_thirds
-- name    : GuthMaynard.energy_le_of_large_values_of_two_thirds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T18:17:35.849593+00:00
-- url     : https://prove2.me/theorems/a8ecd370-fe9e-4d02-b35c-4a358b751cc4
-- title:
--   Lemma 1.7 — additive energy of a large-value set
-- statement:
--   For every $\varepsilon > 0$ there is $T_0$ such that for all $T \ge T_0$, every integer $N$ with $T^{2/3} \le N \le T$, every $\sigma > 1/2$, all complex $(b_n)$ with $|b_n| \le 1$, and every finite $W \subseteq [0, T]$ any two points of which are at distance at least $1$: if $\big|\sum_{N < n \le 2N} b_n n^{it}\big| > N^\sigma$ for all $t \in W$, then
--   $$E(W) \le |W|^3N^{1-2\sigma+\varepsilon} + |W|^2N^{2-2\sigma+\varepsilon},$$
--   where $E(W)$ is the number of $(w_1, w_2, w_3, w_4) \in W^4$ with $|w_1 + w_2 - w_3 - w_4| \le 1$ (`energy W`).
--
--   **Formalization note.** The $o(1)$ in the exponents is read with §1.2's convention ($T \to \infty$), uniformly in $N$, $\sigma$, $(b_n)$ and $W$.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 5, Lemma 1.7

import Mathlib
import Definitions.Def_GuthMaynard

namespace GuthMaynard

theorem energy_le_of_large_values_of_two_thirds :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ),
      (N : ℝ) ∈ Set.Icc (T ^ (2 / 3 : ℝ)) T → ∀ σ : ℝ, 1 / 2 < σ → ∀ b : ℕ → ℂ,
      (∀ n, ‖b n‖ ≤ 1) → ∀ W : Finset ℝ, IsSeparated 1 W → (∀ t ∈ W, t ∈ Set.Icc 0 T) →
      (∀ t ∈ W, (N : ℝ) ^ σ <
        ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖) →
      (energy W : ℝ) ≤ (W.card : ℝ) ^ 3 * (N : ℝ) ^ (1 - 2 * σ + ε) +
        (W.card : ℝ) ^ 2 * (N : ℝ) ^ (2 - 2 * σ + ε) := by
  sorry

end GuthMaynard
