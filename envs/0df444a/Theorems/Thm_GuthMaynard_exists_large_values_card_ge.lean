-- Prove2me | Theorems.Thm_GuthMaynard_exists_large_values_card_ge
-- name    : GuthMaynard.exists_large_values_card_ge
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T18:15:17.469192+00:00
-- url     : https://prove2.me/theorems/4561ee83-19d7-4931-8dc3-7139170ef568
-- title:
--   §1.1, footnote 1 — Dirichlet polynomials with N^{2−2σ} large values
-- statement:
--   There is $c > 0$ such that for every $\sigma \in (1/2, 1)$ there is $N_0$ such that for every integer $N \ge N_0$ and every $T \ge N$ there are complex $(b_n)$ with $|b_n| \le 1$ and a finite set $W \subseteq [0, T]$, any two points of which are at distance at least $1$, such that
--   $$\Big|\sum_{N < n \le 2N} b_n n^{it}\Big| > N^\sigma \quad (t \in W) \qquad\text{and}\qquad |W| \ge c\,N^{2-2\sigma}.$$
--
--   **Formalization note.** The sentence's $W$ is the Main Question's on the same page: a $1$-separated subset of $[0,T]$ where $|D(t)| > N^\sigma$. "$|W| \gg N^{2-2\sigma}$" is read as $|W| \ge c\,N^{2-2\sigma}$ for all large $N$, with $c$ an absolute constant, as §1.2 defines $\gg$ (p. 5). How large $N$ must be may depend on $\sigma$.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 3, §1.1, footnote 1

import Mathlib
import Definitions.Def_GuthMaynard

namespace GuthMaynard

theorem exists_large_values_card_ge :
    ∃ c : ℝ, 0 < c ∧ ∀ σ : ℝ, σ ∈ Set.Ioo (1 / 2 : ℝ) 1 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ T : ℝ, (N : ℝ) ≤ T →
      ∃ (b : ℕ → ℂ) (W : Finset ℝ), (∀ n, ‖b n‖ ≤ 1) ∧ IsSeparated 1 W ∧
        (∀ t ∈ W, t ∈ Set.Icc 0 T ∧
          (N : ℝ) ^ σ < ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖) ∧
        c * (N : ℝ) ^ (2 - 2 * σ) ≤ W.card := by
  sorry

end GuthMaynard
