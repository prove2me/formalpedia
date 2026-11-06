-- Prove2me | Theorems.Thm_GuthMaynard_card_le_of_large_smoothedPoly_Iterm
-- name    : GuthMaynard.card_le_of_large_smoothedPoly_Iterm
-- status  : Disproved
-- author  : @dbenbenn
-- created : 2026-11-05T19:12:19.0492+00:00
-- url     : https://prove2.me/theorems/d1c7e6f3-e96b-44bc-95b3-10c484eafb0d
-- title:
--   Proposition 4.6 — |W| bounded in terms of the sum of the I_m
-- statement:
--   Let $w$ be a weight as in §3 (`IsWeight w`) and $\varepsilon > 0$. There is a constant $C$ such that for every $T$, every integer $N$ with $T^{3/4} \le N \le T$, every real $\sigma$, all complex $(b_n)$ with $|b_n| \le 1$, and every finite set $W$ contained in an interval $[a, a+T]$ whose distinct points are at distance at least $T^\varepsilon$: if $|D_N(t)| > N^\sigma$ for all $t \in W$, then
--   $$|W| \le C\Big(N^{2-2\sigma} + N^{1-2\sigma}\Big(\sum_{m \in \mathbb Z^3\setminus\{0\}} I_m\Big)^{1/3}\Big),$$
--   where $I_m = N^3\sum_{t_1,t_2,t_3 \in W}\widehat h_{t_1-t_2}(m_1N)\,\widehat h_{t_2-t_3}(m_2N)\,\widehat h_{t_3-t_1}(m_3N)$ (`Iterm w N W m`), with $\widehat h_t$ the Fourier transform of $h_t(u) = w(u)^2u^{it}$.
--
--   **Formalization note.**
--   - **Standing assumptions.** The paper states no range for $N$ in this proposition. §4 opens the proof of Proposition 3.1 (p. 10), whose statement has $T = N^{6/5}$ (p. 9). The proof of Proposition 12.1 applies the same bounds, through (12.1), for $T^{5/6} \le N \le T$ (p. 47). Proposition 11.1 states $T^{3/4} \le N \le T$ (p. 38), and Proposition 11.2 states $N \ge T^{3/4}$ (p. 39). The statement assumes $T^{3/4} \le N \le T$, which contains the ranges of Propositions 3.1, 11.1 and 12.1; this is a choice of the formalization. It also assumes that $W$ lies in an interval of length $T$, as the paper uses on p. 15 (before (5.4)); the proposition itself states only that $W$ is $T^\epsilon$-separated.
--   - **The cube root.** The paper treats $\sum_{m\ne0}I_m$ as a real number. The statement takes the real part $s$ of the sum and its real cube root, written $\operatorname{sign}(s)\,|s|^{1/3}$, as printed.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 15, Proposition 4.6

import Mathlib
import Definitions.Def_GuthMaynard

namespace GuthMaynard

theorem card_le_of_large_smoothedPoly_Iterm (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (T : ℝ) (N : ℕ), (N : ℝ) ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T → ∀ (σ : ℝ) (b : ℕ → ℂ),
      (∀ n, ‖b n‖ ≤ 1) → ∀ (W : Finset ℝ) (a : ℝ), IsSeparated (T ^ ε) W →
      (∀ t ∈ W, t ∈ Set.Icc a (a + T)) → (∀ t ∈ W, (N : ℝ) ^ σ < ‖smoothedPoly w N b t‖) →
      let s : ℝ := (∑' m : {m : Fin 3 → ℤ // m ≠ 0}, Iterm w N W m).re
      (W.card : ℝ) ≤ C * ((N : ℝ) ^ (2 - 2 * σ) + (N : ℝ) ^ (1 - 2 * σ) * (Real.sign s * |s| ^ (1 / 3 : ℝ))) := by
  sorry

end GuthMaynard
