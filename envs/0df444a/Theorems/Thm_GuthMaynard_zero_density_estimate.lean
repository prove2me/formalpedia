-- Prove2me | Theorems.Thm_GuthMaynard_zero_density_estimate
-- name    : GuthMaynard.zero_density_estimate
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T18:14:03.953053+00:00
-- url     : https://prove2.me/theorems/10ef4104-9911-478b-bf25-82f640496795
-- title:
--   Theorem 1.2 (Zero density estimate)
-- statement:
--   For every $\sigma \in [1/2, 1]$ and every $\varepsilon > 0$ there is a constant $C$ such that, for all sufficiently large $T$,
--   $$N(\sigma, T) \le C\,T^{15(1-\sigma)/(3+5\sigma) + \varepsilon},$$
--   where $N(\sigma, T)$ is `LindelofHypothesis.zeroDensityCount σ T`: the number of zeros $\rho$ of $\zeta$ with $\operatorname{Re}\rho \ge \sigma$ and $|\operatorname{Im}\rho| \le T$, counted with multiplicity, in $\mathbb N \cup \{\infty\}$.
--
--   **Formalization note.** The statement has the same shape as the published (1.2), (1.3) and (1.4) items it sits beside. $T^{o(1)}$ is read for each fixed $\sigma$ as "$\le C\,T^{\varepsilon}$ for every $\varepsilon > 0$ and large $T$". The range $\sigma \in [1/2, 1]$ is not printed; it is the range the paper works in.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 2, Theorem 1.2 (Zero density estimate)

import Mathlib
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open Filter
open scoped ENNReal

namespace GuthMaynard

theorem zero_density_estimate (σ : ℝ) (hσ₀ : 1 / 2 ≤ σ) (hσ₁ : σ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ T in atTop,
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ (15 * (1 - σ) / (3 + 5 * σ) + ε)) := by
  sorry

end GuthMaynard
