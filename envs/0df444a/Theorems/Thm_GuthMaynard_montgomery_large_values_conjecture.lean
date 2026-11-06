-- Prove2me | Theorems.Thm_GuthMaynard_montgomery_large_values_conjecture
-- name    : GuthMaynard.montgomery_large_values_conjecture
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T18:16:01.284361+00:00
-- url     : https://prove2.me/theorems/fcbac013-5909-4e80-b408-6c8b495d0fc7
-- title:
--   Conjecture 1.5 (Montgomery's large value conjecture)
-- statement:
--   For every $\sigma > 1/2$ there is a constant $C$ such that for every $\varepsilon > 0$ there is $T_0$ with the following property. For all $T \ge T_0$, all integers $N \ge 0$, all complex $(b_n)$ with $|b_n| \le 1$, and every finite $W \subseteq [0, T]$ any two points of which are at distance at least $1$: if $\big|\sum_{N < n \le 2N} b_n n^{it}\big| > N^\sigma$ for all $t \in W$, then
--   $$|W| \le C\,T^{\varepsilon}N^{2-2\sigma}.$$
--
--   **Formalization note.** $C(\sigma)T^{o(1)}$ is read as a constant depending only on $\sigma$ times $T^{\varepsilon}$ for every $\varepsilon > 0$ and all large $T$, uniformly in $N$, $(b_n)$ and $W$. This is an open conjecture: the paper states it and proves it in no range of its own; (1.1) gives it when $N^\sigma > N^{1/2}T^{1/4}$ (p. 4).
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 4, Conjecture 1.5 (Montgomery's large value conjecture)

import Mathlib
import Definitions.Def_GuthMaynard

namespace GuthMaynard

theorem montgomery_large_values_conjecture (σ : ℝ) (hσ : 1 / 2 < σ) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ) (b : ℕ → ℂ),
      (∀ n, ‖b n‖ ≤ 1) → ∀ W : Finset ℝ, IsSeparated 1 W → (∀ t ∈ W, t ∈ Set.Icc 0 T) →
      (∀ t ∈ W, (N : ℝ) ^ σ <
        ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖) →
      (W.card : ℝ) ≤ C * T ^ ε * (N : ℝ) ^ (2 - 2 * σ) := by
  sorry

end GuthMaynard
