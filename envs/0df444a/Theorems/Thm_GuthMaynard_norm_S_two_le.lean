-- Prove2me | Theorems.Thm_GuthMaynard_norm_S_two_le
-- name    : GuthMaynard.norm_S_two_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T19:13:33.167196+00:00
-- url     : https://prove2.me/theorems/69306713-e1c4-4dd6-bf7f-3ee2017a52fe
-- title:
--   Proposition 6.1 (S₂ bound)
-- statement:
--   Let $w$ be a weight as in §3 (`IsWeight w`), $\varepsilon > 0$ and $k \ge 1$. For every $\delta > 0$ there are $C$ and $T_0$ such that for all $T \ge T_0$, every integer $N$ with $T^{3/4} \le N \le T$, and every finite set $W$ contained in an interval $[a, a+T]$ whose distinct points are at distance at least $T^\varepsilon$,
--   $$|S_2| \le C\,T^{\delta}\Big(N^2|W|^2 + TN|W|^{2-1/k} + N^2|W|^2\Big(\frac{T^{1/2}}{|W|^{3/4}}\Big)^{1/k}\Big),$$
--   where $S_2$ (`S 2 w N W`) is the sum of $I_m$ over the $m \in \mathbb Z^3$ with exactly two nonzero coordinates.
--
--   **Formalization note.** $\lessapprox_{\epsilon,k}$ is §1.2's convention: for every $\delta > 0$, a constant depending on $\delta$, $\epsilon$, $k$ (and the fixed $w$) times $T^\delta$, for all large $T$. The paper states no range for $N$ in this proposition. §4 opens the proof of Proposition 3.1 (p. 10), whose statement has $T = N^{6/5}$ (p. 9). The proof of Proposition 12.1 applies the same bounds, through (12.1), for $T^{5/6} \le N \le T$ (p. 47). Proposition 11.1 states $T^{3/4} \le N \le T$ (p. 38), and Proposition 11.2 states $N \ge T^{3/4}$ (p. 39). The statement assumes $T^{3/4} \le N \le T$, which contains the ranges of Propositions 3.1, 11.1 and 12.1; this is a choice of the formalization. It also assumes that $W$ lies in an interval of length $T$, as the paper uses on p. 15 (before (5.4)); the proposition itself states only that $W$ is $T^\epsilon$-separated.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 16, Proposition 6.1 (S₂ bound)

import Mathlib
import Definitions.Def_GuthMaynard

namespace GuthMaynard

theorem norm_S_two_le (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 1 ≤ k) :
    ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ),
      (N : ℝ) ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T → ∀ (W : Finset ℝ) (a : ℝ), IsSeparated (T ^ ε) W →
      (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
      ‖S 2 w N W‖ ≤ C * T ^ δ * ((N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 +
        T * N * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
        (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 * (T ^ (1 / 2 : ℝ) / (W.card : ℝ) ^ (3 / 4 : ℝ)) ^ (1 / (k : ℝ))) := by
  sorry

end GuthMaynard
