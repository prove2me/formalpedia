-- Prove2me | Theorems.Thm_GuthMaynard_zeroDensityCount_le_uniform
-- name    : GuthMaynard.zeroDensityCount_le_uniform
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T19:17:36.339204+00:00
-- url     : https://prove2.me/theorems/a928c521-b688-4f0a-be61-0e2fd3bde536
-- title:
--   (13.3) — the zero density bound uniformly up to σ = 1
-- statement:
--   There are constants $C$ and $A$ and a function $e(T)$ with $e(T) \to 0$ as $T \to \infty$ such that
--   $$N(\sigma, T) \le C\,T^{(30/13+e(T))(1-\sigma)}(\log T)^A$$
--   for all $T \ge 2$ and all $\sigma \in [1/2, 1]$. Here $N(\sigma, T)$ is `LindelofHypothesis.zeroDensityCount σ T`, the number of zeros $\rho$ of $\zeta$ with $\operatorname{Re}\rho \ge \sigma$ and $|\operatorname{Im}\rho| \le T$, counted with multiplicity.
--
--   **Formalization note.** The display is read literally. The $o(1)$ is one function $e(T) \to 0$, the constant is absolute, and $(\log T)^{O(1)}$ is one fixed power $A$, all uniform in $\sigma$. Unlike (1.4), the $o(1)$ multiplies $1 - \sigma$, so the bound stays strong as $\sigma \to 1$. That is what the proofs of Corollaries 1.3 and 1.4 use.
-- source:
--   Guth, L. and Maynard, J., New large value estimates for Dirichlet polynomials, Ann. of Math. (2) 203 (2026) 623–675, https://doi.org/10.4007/annals.2026.203.2.6 (arXiv:2405.20552v2, whose page numbers are used), p. 50, (13.3)

import Mathlib
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open Filter Topology
open scoped ENNReal

namespace GuthMaynard

theorem zeroDensityCount_le_uniform :
    ∃ (C A : ℝ) (e : ℝ → ℝ), Tendsto e atTop (𝓝 0) ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, σ ∈ Set.Icc (1 / 2 : ℝ) 1 →
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ ((30 / 13 + e T) * (1 - σ)) * Real.log T ^ A) := by
  sorry

end GuthMaynard
