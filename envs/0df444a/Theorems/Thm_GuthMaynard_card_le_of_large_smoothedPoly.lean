-- Prove2me | Theorems.Thm_GuthMaynard_card_le_of_large_smoothedPoly
-- name    : GuthMaynard.card_le_of_large_smoothedPoly
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T18:18:24.163357+00:00
-- url     : https://prove2.me/theorems/f8465122-cf0e-411b-abe6-83f4c28ae371
-- title:
--   Proposition 3.1 — the main proposition, for T = N^{6/5}
-- statement:
--   Let $w$ be a weight as in §3 (`IsWeight w`) and $\varepsilon > 0$. For every $\delta > 0$ there is $N_0$ such that, writing $T = N^{6/5}$: for every integer $N \ge N_0$, every $\sigma \in [7/10, 8/10]$, all complex $(b_n)$ with $|b_n| \le 1$, and every finite set $W$ contained in an interval $[a, a+T]$ whose distinct points are at distance at least $T^{\varepsilon}$, if $|D_N(t)| \ge N^\sigma$ for all $t \in W$, where $D_N(t) = \sum_n w(n/N)\,b_n n^{it}$ (`smoothedPoly w N b t`), then
--   $$|W| \le T\,N^{(12-20\sigma)/5 + \delta}.$$
--
--   **Formalization note.** $o_\epsilon(1)$ is read as $N \to \infty$ (equivalently $T \to \infty$), uniformly in $\sigma$, $(b_n)$ and $W$, with the threshold depending on $\varepsilon$ and on the fixed weight $w$.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 9, Proposition 3.1

import Mathlib
import Definitions.Def_GuthMaynard

namespace GuthMaynard

theorem card_le_of_large_smoothedPoly (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) :
    ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ σ : ℝ, σ ∈ Set.Icc (7 / 10 : ℝ) (8 / 10) →
      ∀ b : ℕ → ℂ, (∀ n, ‖b n‖ ≤ 1) → ∀ (W : Finset ℝ) (a : ℝ),
      IsSeparated (((N : ℝ) ^ (6 / 5 : ℝ)) ^ ε) W →
      (∀ t ∈ W, t ∈ Set.Icc a (a + (N : ℝ) ^ (6 / 5 : ℝ))) →
      (∀ t ∈ W, (N : ℝ) ^ σ ≤ ‖smoothedPoly w N b t‖) →
      (W.card : ℝ) ≤ (N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ ((12 - 20 * σ) / 5 + δ) := by
  sorry

end GuthMaynard
