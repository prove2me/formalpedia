-- Prove2me | Theorems.Thm_GuthMaynard_zeroDensityCount_le_uniform_interior
-- name    : GuthMaynard.zeroDensityCount_le_uniform_interior
-- status  : Open
-- author  : @nonlocally
-- created : 2026-11-05T22:15:02.496381+00:00
-- url     : https://prove2.me/theorems/5627da54-3b51-49be-b77c-78c7f45ab5e8
-- title:
--   Interior uniform form of the zero-density bound (13.3)
-- statement:
--   Let $N(\sigma,T)$ denote the number of zeros $\rho$ of the Riemann zeta function with $\operatorname{Re}\rho\ge\sigma$ and $|\operatorname{Im}\rho|\le T$, counted with multiplicity. There are a real constant $C$ and a function $e(T)$ tending to zero such that, for every $T\ge2$ and every $\sigma\in[1/2,4/5]$,
--
--   $$
--   N(\sigma,T)\le C\,T^{(30/13+e(T))(1-\sigma)}(\log T)^{44}.
--   $$
--
--   The same $C$ and $e$ work throughout the stated interval. This is the interior-range form of the uniform zero-density bound in (13.3), with one absolute logarithmic power. It is reusable in arguments that handle a neighborhood of $\sigma=1$ separately.
--
--   **Formalization Note.** The zero count is valued in $\mathbb N\cup\{\infty\}$ and then coerced to $[0,\infty]$. Both displayed powers use real exponents, and the right-hand side is converted with `ENNReal.ofReal`.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://arxiv.org/abs/2405.20552v2, p. 50, equation (13.3); the main estimate (1.4) on p. 4, restricted here to 1/2 ≤ σ ≤ 4/5.

import Mathlib
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open Filter Topology
open scoped ENNReal

namespace GuthMaynard

theorem zeroDensityCount_le_uniform_interior :
    ∃ (C : ℝ) (e : ℝ → ℝ), Tendsto e atTop (𝓝 0) ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ,
      σ ∈ Set.Icc (1 / 2 : ℝ) (4 / 5 : ℝ) →
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ ((30 / 13 + e T) * (1 - σ)) * Real.log T ^ (44 : ℝ)) := by
  sorry

end GuthMaynard
