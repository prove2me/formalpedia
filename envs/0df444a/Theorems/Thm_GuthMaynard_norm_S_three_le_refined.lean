-- Prove2me | Theorems.Thm_GuthMaynard_norm_S_three_le_refined
-- name    : GuthMaynard.norm_S_three_le_refined
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T19:14:43.897297+00:00
-- url     : https://prove2.me/theorems/885fd961-9958-4ac9-9501-afcf2aca5657
-- title:
--   Proposition 10.1 (Refined S₃ bound)
-- statement:
--   Let $w$ be a weight as in §3 (`IsWeight w`) and $\varepsilon > 0$. For every $\delta > 0$ there are $C$ and $T_0$ such that for all $T \ge T_0$, every integer $N$ with $T^{3/4} \le N \le T$, and every finite set $W$ contained in an interval $[a, a+T]$ whose distinct points are at distance at least $T^\varepsilon$,
--   $$|S_3| \le C\,T^{\delta}\Big(T^2|W|^{3/2} + TN|W|^{1/2}E(W)^{1/2}\Big),$$
--   where $S_3$ (`S 3 w N W`) is the sum of $I_m$ over the $m \in \mathbb Z^3$ with all coordinates nonzero, and $E(W)$ is the additive energy (`energy W`).
--
--   **Formalization note.** $\lessapprox_\epsilon$ is §1.2's convention, with the constant allowed to depend on the fixed $w$. The paper states no range for $N$ in this proposition. §4 opens the proof of Proposition 3.1 (p. 10), whose statement has $T = N^{6/5}$ (p. 9). The proof of Proposition 12.1 applies the same bounds, through (12.1), for $T^{5/6} \le N \le T$ (p. 47). Proposition 11.1 states $T^{3/4} \le N \le T$ (p. 38), and Proposition 11.2 states $N \ge T^{3/4}$ (p. 39). The statement assumes $T^{3/4} \le N \le T$, which contains the ranges of Propositions 3.1, 11.1 and 12.1; this is a choice of the formalization.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 36, Proposition 10.1 (Refined S₃ bound)

import Mathlib
import Definitions.Def_GuthMaynard

namespace GuthMaynard

theorem norm_S_three_le_refined (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) :
    ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ),
      (N : ℝ) ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T → ∀ (W : Finset ℝ) (a : ℝ), IsSeparated (T ^ ε) W →
      (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
      ‖S 3 w N W‖ ≤ C * T ^ δ * (T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
        T * N * (W.card : ℝ) ^ (1 / 2 : ℝ) * (energy W : ℝ) ^ (1 / 2 : ℝ)) := by
  sorry

end GuthMaynard
