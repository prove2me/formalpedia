-- Prove2me | Theorems.Thm_OWMR_renewalMeasure_Ico_lt_top
-- name    : OWMR.renewalMeasure_Ico_lt_top
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T02:42:43.369381+00:00
-- url     : https://prove2.me/theorems/51d195b4-e293-4d3a-8a9c-ac4dc26e7c4c
-- title:
--   Finiteness of the renewal function: $M(w)=U[0,w)<\infty$
-- statement:
--   Let $\rho$ be the law of a nonnegative demand $D$ with positive mean, $\mathbb E D>0$, and let $U$ be its renewal measure, $U(A)=\sum_{n\ge0}\mathbb P(D^{(n)}\in A)$. Then for every real $w$,
--
--   $$M(w)=U[0,w)<\infty .$$
--
--   So $U$ is finite on bounded sets, and the expected number of periods for cumulative demand to reach any level is finite.
--
--   **Formalization Note** Positive mean is stated as $\int^{-}x\,\rho(dx)>0$ (a lower Lebesgue integral in $[0,\infty]$).
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 4.2, footnote to eq. (9), p. 12 ("Thus, U is finite on bounded sets") and the sentence after (9).

import Definitions.Def_owmr_renewal

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem renewalMeasure_Ico_lt_top (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (w : ℝ) : renewalMeasure ρ (Set.Ico 0 w) < ∞ := by sorry
end OWMR
