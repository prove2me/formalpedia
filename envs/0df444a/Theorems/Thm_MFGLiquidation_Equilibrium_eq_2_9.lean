-- Prove2me | Theorems.Thm_MFGLiquidation_Equilibrium_eq_2_9
-- name    : MFGLiquidation.Equilibrium.eq_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:37.71701+00:00
-- url     : https://prove2.me/theorems/8709af42-d9f2-4282-b68c-1c8bfff9dfaf
-- title:
--   (2.9) — exp(−∫_r^s A_u/(2η_u) du) ≤ ((T − s)/(T − r))^α for 0 ≤ r ≤ s < T
-- statement:
--   Under Assumption 2.3, let $(A,Z^A)$ solve the singular Riccati BSDE of Lemma A.1 and let $\alpha=\eta_\star/\|\eta\|$. Then almost surely, for all $0\le r\le s<T$,
--   $$\exp\Big(-\int_r^s\frac{A_u}{2\eta_u}\,du\Big)\le\Big(\frac{T-s}{T-r}\Big)^{\alpha}.$$
--   This is the decay estimate that turns the explicit solution formula for $X$ into membership of $\mathcal H_\alpha$: the fundamental solution of $dX=-\frac{A}{2\eta}X\,dt$ decays at least like $(T-t)^\alpha$.
--
--   **Formalization Note** The range is $0\le r\le s<T$ as printed; $s=T$ is excluded (the integral diverges there). $\alpha$ is computed from the essential bounds of $\eta$.
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, p. 9, (2.9)

import Mathlib
import Definitions.Def_MFGLiquidation_Equilibrium_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLiquidation.Equilibrium

open Peng1990.SMP

theorem eq_2_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (D : Data Ω k) (hD : D.Standing P) (hA : D.Assumption23 P hD)
    (A : ℝ≥0 → Ω → ℝ) (ZA : Fin (k + 1) → ℝ≥0 → Ω → ℝ) (hR : IsSingularRiccati hD A ZA) :
    ∀ᵐ ω ∂P, ∀ r s : ℝ≥0, r ≤ s → s < D.T →
      Real.exp (-∫ u in Set.Icc (r : ℝ) s, A u.toNNReal ω / (2 * D.η u.toNNReal ω)) ≤
        (((D.T : ℝ) - s) / ((D.T : ℝ) - r)) ^ D.alpha P := by sorry

end MFGLiquidation.Equilibrium
