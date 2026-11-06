-- Prove2me | Theorems.Thm_GuthMaynard_norm_S_three_le
-- name    : GuthMaynard.norm_S_three_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T19:15:35.324218+00:00
-- url     : https://prove2.me/theorems/7edf57c9-e148-405c-b5f6-9167d4d2fea8
-- title:
--   Proposition 11.2 (S₃ Bound)
-- statement:
--   Let $w$ be a weight as in §3 (`IsWeight w`) and $\varepsilon > 0$. For every $\delta > 0$ there are $C$ and $T_0$ such that for all $T \ge T_0$, every integer $N$ with $T^{3/4} \le N \le T$, every real $\sigma$, all complex $(b_n)$ with $|b_n| \le 1$, and every finite set $W$ contained in an interval $[a, a+T]$ whose distinct points are at distance at least $T^\varepsilon$: if $|D_N(t)| \ge N^\sigma$ for all $t \in W$, where $D_N(t) = \sum_n w(n/N)\,b_nn^{it}$ (`smoothedPoly w N b t`), then
--   $$|S_3| \le C\,T^{\delta}\Big(T^2|W|^{3/2} + T|W|N^{3-2\sigma} + T|W|^2N^{3/2-\sigma} + T^{9/8}|W|^{29/16}N^{3/2-\sigma}\Big),$$
--   where $S_3$ (`S 3 w N W`) is the sum of $I_m$ over the $m \in \mathbb Z^3$ with all coordinates nonzero.
--
--   **Formalization note.**
--   - The proposition names only $N \ge T^{3/4}$. The sentence before it says it comes from "substituting the bound of Proposition 11.1 (applied to $D_N(t)$) into Proposition 10.1", so the hypotheses are those two propositions': $W$ is $T^\epsilon$-separated in an interval of length $T$, $N \le T$, $|b_n| \le 1$, and $|D_N| \ge N^\sigma$ on $W$.
--   - $\lessapprox$ is §1.2's convention, with the constant allowed to depend on $\epsilon$ and the fixed $w$.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 39, Proposition 11.2 (S₃ Bound)

import Mathlib
import Definitions.Def_GuthMaynard

namespace GuthMaynard

theorem norm_S_three_le (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) :
    ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ),
      (N : ℝ) ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T → ∀ (σ : ℝ) (b : ℕ → ℂ), (∀ n, ‖b n‖ ≤ 1) →
      ∀ (W : Finset ℝ) (a : ℝ), IsSeparated (T ^ ε) W → (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
      (∀ t ∈ W, (N : ℝ) ^ σ ≤ ‖smoothedPoly w N b t‖) →
      ‖S 3 w N W‖ ≤ C * T ^ δ * (T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
        T * (W.card : ℝ) * (N : ℝ) ^ (3 - 2 * σ) +
        T * (W.card : ℝ) ^ 2 * (N : ℝ) ^ (3 / 2 - σ) +
        T ^ (9 / 8 : ℝ) * (W.card : ℝ) ^ (29 / 16 : ℝ) * (N : ℝ) ^ (3 / 2 - σ)) := by
  sorry

end GuthMaynard
