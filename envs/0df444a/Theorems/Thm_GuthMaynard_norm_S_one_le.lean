-- Prove2me | Theorems.Thm_GuthMaynard_norm_S_one_le
-- name    : GuthMaynard.norm_S_one_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T19:12:57.492291+00:00
-- url     : https://prove2.me/theorems/4edcd3c1-4567-46b2-93c1-af38cbaa0e85
-- title:
--   Proposition 5.1 (S₁ bound)
-- statement:
--   Let $w$ be a weight as in §3 (`IsWeight w`) and $\varepsilon > 0$. There is a constant $C$ such that for every $T$, every integer $N$ with $T^{3/4} \le N \le T$, and every finite set $W$ contained in an interval $[a, a+T]$ whose distinct points are at distance at least $T^\varepsilon$,
--   $$|S_1| \le C\,T^{-10},$$
--   where $S_1$ (`S 1 w N W`) is the sum of $I_m$ over the $m \in \mathbb Z^3$ with exactly one nonzero coordinate.
--
--   **Formalization note.** The proposition carries no hypotheses of its own. The paper states no range for $N$ in this proposition. §4 opens the proof of Proposition 3.1 (p. 10), whose statement has $T = N^{6/5}$ (p. 9). The proof of Proposition 12.1 applies the same bounds, through (12.1), for $T^{5/6} \le N \le T$ (p. 47). Proposition 11.1 states $T^{3/4} \le N \le T$ (p. 38), and Proposition 11.2 states $N \ge T^{3/4}$ (p. 39). The statement assumes $T^{3/4} \le N \le T$, which contains the ranges of Propositions 3.1, 11.1 and 12.1; this is a choice of the formalization. It also assumes that $W$ lies in an interval of length $T$, as the paper uses on p. 15 (before (5.4)); the proposition itself states only that $W$ is $T^\epsilon$-separated.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 16, Proposition 5.1 (S₁ bound)

import Mathlib
import Definitions.Def_GuthMaynard

namespace GuthMaynard

theorem norm_S_one_le (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (T : ℝ) (N : ℕ), (N : ℝ) ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T →
      ∀ (W : Finset ℝ) (a : ℝ), IsSeparated (T ^ ε) W → (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
      ‖S 1 w N W‖ ≤ C * T ^ (-10 : ℝ) := by
  sorry

end GuthMaynard
