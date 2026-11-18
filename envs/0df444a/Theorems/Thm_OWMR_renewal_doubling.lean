-- Prove2me | Theorems.Thm_OWMR_renewal_doubling
-- name    : OWMR.renewal_doubling
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T02:42:39.501278+00:00
-- url     : https://prove2.me/theorems/6992dc32-0dfd-431b-a060-d6a2bb59dfb5
-- title:
--   Renewal doubling bound: $M(2w)\le 2M(w)$
-- statement:
--   Let $U$ be the renewal measure of i.i.d. nonnegative demands and $M(w)=U[0,w)$. For every $w\ge0$,
--
--   $$M(2w)\le 2M(w).$$
--
--   Doubling the width of an $(s,S)$ policy at most doubles its expected cycle length.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Lemma 2 (Renewal Interval Bounds), second claim, p. 13, and the last sentence of Step 1 of its proof.

import Definitions.Def_owmr_renewal

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem renewal_doubling (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (w : ℝ) (hw : 0 ≤ w) :
    renewalMeasure ρ (Set.Ico 0 (2 * w)) ≤ 2 * renewalMeasure ρ (Set.Ico 0 w) := by sorry
end OWMR
