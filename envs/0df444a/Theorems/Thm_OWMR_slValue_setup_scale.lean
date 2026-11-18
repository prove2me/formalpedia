-- Prove2me | Theorems.Thm_OWMR_slValue_setup_scale
-- name    : OWMR.slValue_setup_scale
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T01:17:29.424749+00:00
-- url     : https://prove2.me/theorems/4e431a08-2b41-4019-b4cb-3baa48c4f05b
-- title:
--   Scaling a setup cost by $a\ge1$ scales the value by at most $a$
-- statement:
--   Let $\rho$ be a probability law of demand on $[0,\infty)$ and $f\ge0$ a nonnegative one-period holding and backlog cost, and write $\mathcal J_\rho(f;K)$ for the optimal long-run average cost of the single-location problem with i.i.d. demands of law $\rho$ and setup cost $K$. For every real $K$ and every $a\ge1$,
--
--   $$\mathcal J_\rho(f;aK)\le a\,\mathcal J_\rho(f;K).$$
--
--   The source uses this in Step 2 of the proof of Theorem 1, with $a=5(\gamma-1)/(3\gamma)$, when $\gamma\ge5/2$.
--
--   **Formalization Note** $\mathcal J_\rho(f;K)$ is `slValue ρ f K`, and the factor $a$ enters through `ENNReal.ofReal`.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 5.4, Step 2 of the proof of Theorem 1 ("multiplying a setup cost by a >= 1 multiplies its value by at most a"), p. 26.

import Definitions.Def_owmr_single_location

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem slValue_setup_scale (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (f : ℝ → ℝ)
    (hf : ∀ y, 0 ≤ f y) (K : ℝ) {a : ℝ} (ha : 1 ≤ a) :
    slValue ρ f (a * K) ≤ ENNReal.ofReal a * slValue ρ f K := by sorry
end OWMR
