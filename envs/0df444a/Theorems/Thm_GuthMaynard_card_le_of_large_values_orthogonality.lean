-- Prove2me | Theorems.Thm_GuthMaynard_card_le_of_large_values_orthogonality
-- name    : GuthMaynard.card_le_of_large_values_orthogonality
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T18:16:35.593602+00:00
-- url     : https://prove2.me/theorems/0265d65b-3fe1-4123-a6c2-2a5e5bf4923d
-- title:
--   (1.6) — the orthogonality bound |W| = O(TN^{1−2σ})
-- statement:
--   There is an absolute constant $C$ such that for every real $\sigma$, every integer $N \ge 1$, every $T \ge N$, all complex $(b_n)$ with $|b_n| \le 1$, and every finite $W \subseteq [0, T]$ any two points of which are at distance at least $1$: if $\big|\sum_{N < n \le 2N} b_n n^{it}\big| > N^\sigma$ for all $t \in W$, then
--   $$|W| \le C\,T N^{1-2\sigma}.$$
--
--   **Formalization note.** $W$, $D$ and $\sigma$ are those of the Main Question (p. 3) and Conjecture 1.5. The $O$ is an absolute constant (§1.2).
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 4, (1.6)

import Mathlib
import Definitions.Def_GuthMaynard

namespace GuthMaynard

theorem card_le_of_large_values_orthogonality :
    ∃ C : ℝ, ∀ (σ : ℝ) (N : ℕ), 1 ≤ N → ∀ T : ℝ, (N : ℝ) ≤ T → ∀ b : ℕ → ℂ,
      (∀ n, ‖b n‖ ≤ 1) → ∀ W : Finset ℝ, IsSeparated 1 W → (∀ t ∈ W, t ∈ Set.Icc 0 T) →
      (∀ t ∈ W, (N : ℝ) ^ σ <
        ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖) →
      (W.card : ℝ) ≤ C * T * (N : ℝ) ^ (1 - 2 * σ) := by
  sorry

end GuthMaynard
