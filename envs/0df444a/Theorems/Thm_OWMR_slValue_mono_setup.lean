-- Prove2me | Theorems.Thm_OWMR_slValue_mono_setup
-- name    : OWMR.slValue_mono_setup
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T01:17:30.201299+00:00
-- url     : https://prove2.me/theorems/950e4b74-bb68-436b-b35b-9988063fdcec
-- title:
--   Single-location values are nondecreasing in the setup cost
-- statement:
--   Let $\rho$ be a probability law of demand on $[0,\infty)$ and $f:\mathbb R\to\mathbb R$ a one-period holding and backlog cost. Write $\mathcal J_\rho(f;K)$ for the optimal long-run average cost of the single-location problem with i.i.d. demands of law $\rho$ and period cost $K\mathbf 1_{\{q_t>0\}}+f(x_t)$, the infimum over all nonanticipative policies with nonnegative orders, possibly randomized. If $K\le K'$, then
--
--   $$\mathcal J_\rho(f;K)\le\mathcal J_\rho(f;K').$$
--
--   The source uses this monotonicity in the proof of Theorem 1 to compare $J_i(5K_i/3)$ with $J_i(\gamma K_i/(\gamma-1))$ and $J_0(K_0+K_{\max})$ with $J_0(\gamma K_0)$.
--
--   **Formalization Note** $\mathcal J_\rho(f;K)$ is `slValue ρ f K`, an extended nonnegative real.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 5.4, Steps 2 and 3 of the proof of Theorem 1 ("single-location values are nondecreasing in setup cost"), p. 26.

import Definitions.Def_owmr_single_location

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem slValue_mono_setup (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (f : ℝ → ℝ) {K K' : ℝ}
    (hK : K ≤ K') : slValue ρ f K ≤ slValue ρ f K' := by sorry
end OWMR
