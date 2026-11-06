-- Prove2me | Theorems.Thm_GuthMaynard_zeroDensityCount_eq_zero_vinogradov_korobov
-- name    : GuthMaynard.zeroDensityCount_eq_zero_vinogradov_korobov
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T19:17:03.328091+00:00
-- url     : https://prove2.me/theorems/31bda919-670e-47b9-9a48-0c1072736162
-- title:
--   The Vinogradov–Korobov zero-free region (p. 50)
-- statement:
--   There are $c > 0$ and $T_0$ such that for all $T \ge T_0$ and all $\sigma \ge 1 - c(\log T)^{-2/3}(\log\log T)^{-1/3}$,
--   $$N(\sigma, T) = 0,$$
--   where $N(\sigma, T)$ is `LindelofHypothesis.zeroDensityCount σ T`, the number of zeros $\rho$ of $\zeta$ with $\operatorname{Re}\rho \ge \sigma$ and $|\operatorname{Im}\rho| \le T$.
--
--   **Formalization note.** "For a suitable constant $c > 0$" is read with $T$ large.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 50, the Vinogradov–Korobov zero-free region, in the proof of Corollaries 1.3 and 1.4, which cites Montgomery, H. L., Topics in multiplicative number theory, Lecture Notes in Math. 227, Springer (1971), Corollary 11.4, https://doi.org/10.1007/BFb0060851

import Mathlib
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

namespace GuthMaynard

theorem zeroDensityCount_eq_zero_vinogradov_korobov :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ,
      1 - c * Real.log T ^ (-(2 / 3) : ℝ) * Real.log (Real.log T) ^ (-(1 / 3) : ℝ) ≤ σ →
      LindelofHypothesis.zeroDensityCount σ T = 0 := by
  sorry

end GuthMaynard
