-- Prove2me | Theorems.Thm_GuthMaynard_card_le_of_large_smoothedPoly_Iterm_pos
-- name    : GuthMaynard.card_le_of_large_smoothedPoly_Iterm_pos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T22:27:43.983321+00:00
-- url     : https://prove2.me/theorems/3f8fc492-282c-49c9-841b-4929c86f004b
-- title:
--   Proposition 4.6 (corrected) — |W| bounded by the positive part of the sum of the I_m
-- statement:
--   Let $w$ be a weight as in §3 (`IsWeight w`) and $\varepsilon > 0$. There is a constant $C$ such that for every $T$, every integer $N$ with $T^{3/4} \le N \le T$, every real $\sigma$, all complex $(b_n)$ with $|b_n| \le 1$, and every finite set $W$ contained in an interval $[a, a+T]$ whose distinct points are at distance at least $T^\varepsilon$: if $|D_N(t)| > N^\sigma$ for all $t \in W$, then
--   $$|W| \le C\Big(N^{2-2\sigma} + N^{1-2\sigma}\max(s, 0)^{1/3}\Big), \qquad s = \operatorname{Re}\sum_{m \in \mathbb Z^3\setminus\{0\}} I_m,$$
--   where $I_m = N^3\sum_{t_1,t_2,t_3 \in W}\widehat h_{t_1-t_2}(m_1N)\,\widehat h_{t_2-t_3}(m_2N)\,\widehat h_{t_3-t_1}(m_3N)$ (`Iterm w N W m`), with $\widehat h_t$ the Fourier transform of $h_t(u) = w(u)^2u^{it}$, and $D_N(t) = \sum_n w(n/N)\,b_n n^{it}$ (`smoothedPoly w N b t`).
--
--   This is Guth–Maynard's Proposition 4.6 (p. 15) with the positive part of the sum under the cube root. The proposition as printed, “$|W| \ll_\epsilon N^{2-2\sigma} + N^{1-2\sigma}\big(\sum_{m \in \mathbb Z^3\setminus\{0\}} I_m\big)^{1/3}$”, was published as `GuthMaynard.card_le_of_large_smoothedPoly_Iterm` with the real cube root of $s$ and is disproved: at $T = N = 2$ the sum can be very negative while $W$ is nonempty. The paper's proof (Lemmas 4.1–4.5, pp. 12–14) bounds $|W|$ through a quantity that equals $s$ up to $O_\epsilon(T^{-100})$ and is never negative, so it gives this form for every $N$ in the range. The range $T^{3/4} \le N \le T$ and the interval of length $T$ are the published statement's.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 15, Proposition 4.6, with the positive part of the sum (the printed form is disproved)

import Mathlib
import Definitions.Def_GuthMaynard

namespace GuthMaynard

theorem card_le_of_large_smoothedPoly_Iterm_pos (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (T : ℝ) (N : ℕ), (N : ℝ) ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T → ∀ (σ : ℝ) (b : ℕ → ℂ),
      (∀ n, ‖b n‖ ≤ 1) → ∀ (W : Finset ℝ) (a : ℝ), IsSeparated (T ^ ε) W →
      (∀ t ∈ W, t ∈ Set.Icc a (a + T)) → (∀ t ∈ W, (N : ℝ) ^ σ < ‖smoothedPoly w N b t‖) →
      let s : ℝ := (∑' m : {m : Fin 3 → ℤ // m ≠ 0}, Iterm w N W m).re
      (W.card : ℝ) ≤ C * ((N : ℝ) ^ (2 - 2 * σ) + (N : ℝ) ^ (1 - 2 * σ) * max s 0 ^ (1 / 3 : ℝ)) := by
  sorry

end GuthMaynard
