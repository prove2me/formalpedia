-- Prove2me | Theorems.Thm_GuthMaynard_huxley_density_estimate_uniform
-- name    : GuthMaynard.huxley_density_estimate_uniform
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T20:22:08.374189+00:00
-- url     : https://prove2.me/theorems/b8b34966-a46b-46c9-b02d-f5e131238ef4
-- title:
--   Huxley (1.9) — N(α, T) ≪ T^{3(1−α)/(3α−1)} (log T)^{44} uniformly in 3/4 ≤ α ≤ 1
-- statement:
--   There is an absolute constant $C$ such that for all $T \ge 2$ and all $\sigma \in [3/4, 1]$,
--   $$N(\sigma, T) \le C\,T^{3(1-\sigma)/(3\sigma-1)}(\log T)^{44},$$
--   where $N(\sigma, T)$ is `LindelofHypothesis.zeroDensityCount σ T`, the number of zeros $\rho$ of $\zeta$ with $\operatorname{Re}\rho \ge \sigma$ and $|\operatorname{Im}\rho| \le T$, counted with multiplicity.
--
--   This is (1.9) of M. N. Huxley, *On the difference between consecutive primes*, Invent. Math. 15 (1972) 164–170, https://doi.org/10.1007/BF01418933, pp. 164–165: “Let $N(\alpha, T)$ denote the number of zeros $\rho = \beta + i\gamma$ of $\zeta(s)$ in the rectangle $\alpha \le \beta \le 1$, $-T \le \gamma \le T$. (1.4)”, with “$l$ denotes $\log T$”, and “$N(\alpha, T) \ll T^{3(1-\alpha)/(3\alpha-1)}l^{44}$ (1.9) uniformly in $3/4 \le \alpha \le 1$”. The paper proves it in §§2–6 (“We prove (1.9) below”). Its fixed-$\sigma$ form with a $T^{\varepsilon}$ loss is `LindelofHypothesis.huxley_density_estimate`. Guth–Maynard (arXiv:2405.20552v2, p. 50) need a bound that loses only logarithmic factors as $\sigma \to 1$ for their (13.3), `GuthMaynard.zeroDensityCount_le_uniform`; this one serves for $\sigma \ge 4/5$, where $3/(3\sigma - 1) \le 15/7 < 30/13$.
--
--   **Formalization note.** The implied constant is absolute and $T \ge 2$; for bounded $T$ the count is bounded, so only the constant changes.
-- source:
--   Huxley, M. N., On the difference between consecutive primes, Invent. Math. 15 (1972) 164–170, https://doi.org/10.1007/BF01418933, pp. 164–165, (1.9), uniformly in 3/4 ≤ α ≤ 1, used for Guth–Maynard (13.3) (arXiv:2405.20552v2, p. 50)

import Mathlib
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open scoped ENNReal

namespace GuthMaynard

theorem huxley_density_estimate_uniform :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 1 →
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ (3 * (1 - σ) / (3 * σ - 1)) * Real.log T ^ 44) := by
  sorry

end GuthMaynard
