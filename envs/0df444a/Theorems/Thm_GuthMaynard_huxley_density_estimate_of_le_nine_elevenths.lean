-- Prove2me | Theorems.Thm_GuthMaynard_huxley_density_estimate_of_le_nine_elevenths
-- name    : GuthMaynard.huxley_density_estimate_of_le_nine_elevenths
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T19:49:58.966087+00:00
-- url     : https://prove2.me/theorems/2f593135-d67b-4664-ad9d-2ac1a4d429a1
-- title:
--   Huxley (1.9) for 3/4 ≤ α ≤ 9/11 — N(α, T) ≪ T^{3(1−α)/(3α−1)} (log T)^{44}
-- statement:
--   There are constants $C$ and $T_0$ such that for all $T \ge T_0$ and all $\sigma \in [3/4, 9/11]$,
--   $$N(\sigma, T) \le C\,T^{3(1-\sigma)/(3\sigma-1)}(\log T)^{44},$$
--   where $N(\sigma, T)$ is `LindelofHypothesis.zeroDensityCount σ T`, the number of zeros $\rho$ of $\zeta$ with $\operatorname{Re}\rho \ge \sigma$ and $|\operatorname{Im}\rho| \le T$, counted with multiplicity.
--
--   This is the first of the two ranges in which M. N. Huxley, *On the difference between consecutive primes*, Invent. Math. 15 (1972) 164–170, https://doi.org/10.1007/BF01418933, proves (1.9), “$N(\alpha, T) \ll T^{3(1-\alpha)/(3\alpha-1)}l^{44}$ … uniformly in $3/4 \le \alpha \le 1$” (pp. 164–165, $l = \log T$). §6, p. 169: “To obtain (1.9) for the range $3/4 \le \alpha \le 9/11$ we put $X = T^{(5-6\alpha)/(12\alpha-4)}$, (6.5) $Y = T^{3/(12\alpha-4)}$, (6.6) the choice for $X$ satisfying (5.5) if $T$ is sufficiently large.” The uniform statement, `GuthMaynard.huxley_density_estimate_uniform`, is reduced to this range, to `GuthMaynard.huxley_density_estimate_of_nine_elevenths_le` and to the Vinogradov–Korobov milestone.
--
--   **Formalization note.** "$T$ sufficiently large" is the threshold $T_0$, and the implied constant is one constant $C$, the same for every $\sigma$ in the range.
-- source:
--   Huxley, M. N., On the difference between consecutive primes, Invent. Math. 15 (1972) 164–170, https://doi.org/10.1007/BF01418933, p. 169, (1.9) in the range 3/4 ≤ α ≤ 9/11 (§6, with (6.5)–(6.6)), used for Guth–Maynard (13.3) (arXiv:2405.20552v2, p. 50)

import Mathlib
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open scoped ENNReal

namespace GuthMaynard

theorem huxley_density_estimate_of_le_nine_elevenths :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 9 / 11 →
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ (3 * (1 - σ) / (3 * σ - 1)) * Real.log T ^ 44) := by
  sorry

end GuthMaynard
