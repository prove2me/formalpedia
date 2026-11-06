-- Prove2me | Theorems.Thm_GuthMaynard_sum_norm_tsum_hHat_sq_le
-- name    : GuthMaynard.sum_norm_tsum_hHat_sq_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T21:22:13.856288+00:00
-- url     : https://prove2.me/theorems/b53ef05a-6731-4b94-9888-0f7045e6bf35
-- title:
--   Bound for ∑ over pairs of |∑_{m≠0} ĥ_{t₁−t₂}(mN)|² (Guth–Maynard §6, (6.1)–(6.4))
-- statement:
--   Let $w$ be a weight as in §3 (`IsWeight w`), $\varepsilon > 0$ and $k \ge 1$. For every $\delta > 0$ there are $C$ and $T_0$ such that for all $T \ge T_0$, every integer $N$ with $T^{3/4} \le N \le T$, and every finite set $W$ contained in an interval $[a, a+T]$ whose distinct points are at distance at least $T^\varepsilon$,
--   $$N^3\sum_{t_1,t_2\in W}\Big|\sum_{m\ne0}\widehat h_{t_1-t_2}(mN)\Big|^2 \le C\,T^{\delta}\Big(N^2|W|^2 + TN|W|^{2-1/k} + N^2|W|^2\Big(\frac{T^{1/2}}{|W|^{3/4}}\Big)^{1/k}\Big),$$
--   where $\widehat h_t(\xi) = \int e(-\xi u)\,w(u)^2u^{it}\,du$ (`hHat w t ξ`), and the sum over $m \ne 0$ is the `tsum` over nonzero integers.
--
--   This is the bound that the proof of Guth–Maynard's Proposition 6.1 derives for $3N^3\widehat h_0(0)\sum_{t_1,t_2}\big|\sum_{m\ne0}\widehat h_{t_1-t_2}(mN)\big|^2$ (pp. 17–19, (6.1)–(6.4), arXiv:2405.20552v2). It is published separately so that the proof of Proposition 6.1 (`GuthMaynard.norm_S_two_le`) fits the verifier's time limit.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), pp. 17–19, proof of Proposition 6.1, (6.1)–(6.4) (a step of that proof)

import Mathlib
import Definitions.Def_GuthMaynard

namespace GuthMaynard

theorem sum_norm_tsum_hHat_sq_le (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) (k : ℕ)
    (hk : 1 ≤ k) :
    ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ N : ℕ,
      (N : ℝ) ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T → ∀ (W : Finset ℝ) (a : ℝ), IsSeparated (T ^ ε) W →
      (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
      (N : ℝ) ^ 3 * ∑ t₁ ∈ W, ∑ t₂ ∈ W,
          ‖∑' z : {z : ℤ // z ≠ 0}, hHat w (t₁ - t₂) ((z : ℤ) * N)‖ ^ 2 ≤
        C * T ^ δ * ((N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 +
          T * N * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
          (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 *
            (T ^ (1 / 2 : ℝ) / (W.card : ℝ) ^ (3 / 4 : ℝ)) ^ (1 / (k : ℝ))) := by
  sorry

end GuthMaynard
