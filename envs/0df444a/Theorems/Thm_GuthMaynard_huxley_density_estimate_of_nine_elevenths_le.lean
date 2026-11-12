-- Prove2me | Theorems.Thm_GuthMaynard_huxley_density_estimate_of_nine_elevenths_le
-- name    : GuthMaynard.huxley_density_estimate_of_nine_elevenths_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T19:50:11.744593+00:00
-- url     : https://prove2.me/theorems/5648a3bd-f629-49a6-a59e-078a59153580
-- title:
--   Huxley (1.9) for 9/11 ≤ α ≤ 1 − 32400 log l/l — N(α, T) ≪ T^{3(1−α)/(3α−1)} (log T)^{44}
-- statement:
--   There are constants $C$ and $T_0$ such that for all $T \ge T_0$ and all $\sigma$ with $9/11 \le \sigma \le 1 - 32400\log\log T/\log T$,
--   $$N(\sigma, T) \le C\,T^{3(1-\sigma)/(3\sigma-1)}(\log T)^{44},$$
--   where $N(\sigma, T)$ is `LindelofHypothesis.zeroDensityCount σ T`, the number of zeros $\rho$ of $\zeta$ with $\operatorname{Re}\rho \ge \sigma$ and $|\operatorname{Im}\rho| \le T$, counted with multiplicity.
--
--   This is the second of the two ranges in which M. N. Huxley, *On the difference between consecutive primes*, Invent. Math. 15 (1972) 164–170, https://doi.org/10.1007/BF01418933, proves (1.9), “$N(\alpha, T) \ll T^{3(1-\alpha)/(3\alpha-1)}l^{44}$ … uniformly in $3/4 \le \alpha \le 1$” (pp. 164–165, $l = \log T$). §6, p. 169: “For $\alpha \ge 9/11$ we use Haneke's bound [1] for $\zeta(s)$: $\zeta(\frac12+it) \ll |t|^{6/37}\log(|t|+e) \ll |t|^{13/80}$. (6.7) … Our estimate for the number of zeros is obtained by summing (4.7) for $a = 2, 3, \dots, 300$. The condition (5.5) is satisfied unless $\alpha \ge 1 - 32400\log l/l$, (6.10) and it is well known that $N(\alpha, T)$ is zero when $T$ is sufficiently large and (6.10) holds, and so (1.9) is still true.” This statement is the range in which Huxley's argument, rather than the zero-free region, gives the bound. The uniform statement, `GuthMaynard.huxley_density_estimate_uniform`, is reduced to this range, to `GuthMaynard.huxley_density_estimate_of_le_nine_elevenths` and to the Vinogradov–Korobov milestone.
--
--   **Formalization note.**
--   - "$T$ sufficiently large" is the threshold $T_0$, and the implied constant is one constant $C$, the same for every $\sigma$ in the range.
--   - The upper end of the range is the complement of (6.10), with $l = \log T$.
-- source:
--   Huxley, M. N., On the difference between consecutive primes, Invent. Math. 15 (1972) 164–170, https://doi.org/10.1007/BF01418933, p. 169, (1.9) in the range 9/11 ≤ α ≤ 1 − 32400 log l/l (§6, with Haneke's bound (6.7)), used for Guth–Maynard (13.3) (arXiv:2405.20552v2, p. 50)

import Mathlib
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open scoped ENNReal

namespace GuthMaynard

theorem huxley_density_estimate_of_nine_elevenths_le :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 9 / 11 ≤ σ →
      σ ≤ 1 - 32400 * Real.log (Real.log T) / Real.log T →
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ (3 * (1 - σ) / (3 * σ - 1)) * Real.log T ^ 44) := by
  sorry

end GuthMaynard
