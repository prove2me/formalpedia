-- Prove2me | Theorems.Thm_OWMR_renewal_interval_bound
-- name    : OWMR.renewal_interval_bound
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T02:42:49.337199+00:00
-- url     : https://prove2.me/theorems/dfe4716d-cd29-4078-b09e-60b729ac96d4
-- title:
--   Renewal interval bound: $U[x,x+w)\le M(w)$
-- statement:
--   Let $U$ be the renewal measure of i.i.d. nonnegative demands with law $\rho$. For every $x\ge0$ and every real $w$,
--
--   $$U[x,x+w)\le U[0,w)=M(w).$$
--
--   In expectation, no half-open interval of length $w$ contains more partial sums $D^{(n)}$ than $[0,w)$. The source proves it at the first passage $\tau_x$ of cumulative demand over $x$: the partial sums from $\tau_x$ on are $D^{(\tau_x)}$ plus an independent copy of the partial-sum process, so their expected number in $[x,x+w)$ is $M(x+w-D^{(\tau_x)})\le M(w)$.
--
--   **Formalization Note** No moment assumption is needed: if $M(w)=\infty$ the bound is trivial, and for $w\le0$ both sides vanish.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Lemma 2 (Renewal Interval Bounds), first claim, p. 13, and Step 1 of its proof.

import Definitions.Def_owmr_renewal

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem renewal_interval_bound (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (x w : ℝ)
    (hx : 0 ≤ x) :
    renewalMeasure ρ (Set.Ico x (x + w)) ≤ renewalMeasure ρ (Set.Ico 0 w) := by sorry
end OWMR
