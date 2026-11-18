-- Prove2me | Theorems.Thm_OWMR_renewal_depletion_mean
-- name    : OWMR.renewal_depletion_mean
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T02:42:39.406551+00:00
-- url     : https://prove2.me/theorems/5fb68652-3ec7-4548-b6bb-d7e7c69bcd37
-- title:
--   Mean depletion bound: $\int_{[0,w)}y\,U(dy)\le \frac w2\,M(w)$
-- statement:
--   Let $U$ be the renewal measure of i.i.d. nonnegative demands and $M(w)=U[0,w)$. For every $w\ge0$,
--
--   $$\int_{[0,w)}y\,U(dy)\le\frac w2\,M(w).$$
--
--   When $M(w)<\infty$ this is the bound $\mathbb E X_w\le w/2$ on the long-run depletion $X_w$ of a width-$w$ policy, whose law is $U(\cdot\cap[0,w))/M(w)$ by the occupation identity (10).
--
--   **Formalization Note** Stated with lower Lebesgue integrals in $[0,\infty]$, so it holds without finiteness assumptions.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Lemma 2 (Renewal Interval Bounds), third claim E X_w <= w/2, p. 13, and Step 2 of its proof; X_w has law U(. ∩ [0,w))/M(w) by eq. (10).

import Definitions.Def_owmr_renewal

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem renewal_depletion_mean (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (w : ℝ)
    (hw : 0 ≤ w) :
    ∫⁻ x in Set.Ico 0 w, ENNReal.ofReal x ∂(renewalMeasure ρ)
      ≤ ENNReal.ofReal (w / 2) * renewalMeasure ρ (Set.Ico 0 w) := by sorry
end OWMR
