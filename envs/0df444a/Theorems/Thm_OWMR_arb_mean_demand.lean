-- Prove2me | Theorems.Thm_OWMR_arb_mean_demand
-- name    : OWMR.arb_mean_demand
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T12:51:36.127199+00:00
-- url     : https://prove2.me/theorems/c3c88ade-29f3-47ec-9e89-b761fd3bca89
-- title:
--   Lemma C.1: mean demand over a cycle is paid for by the cycle cost
-- statement:
--   For retailer $i$ of a network under the standing assumptions and reals $s<S$, let $U$ be the renewal measure of the demand $D_i$. Then
--   $$\min(H_i,p)\,\mathbb E D_i\,\bigl(U[0,S-s)-1\bigr)\le\int_{[0,S-s)}F_i(S-x)\,U(dx).$$
--   In words: over an $(s,S)$ cycle, the expected cost $F_i$ of the post-order positions is at least $\min(H_i,p)$ times the mean demand times the expected number of periods after the first.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Appendix C, Step 1, Lemma C.1 and (C.1), p. E.8.

import Definitions.Def_owmr_consolidation_policy
import Definitions.Def_owmr_renewal

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem arb_mean_demand {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n) (s S : ℝ)
    (hsS : s < S) :
    min (N.H i) N.p * (∫ x, (x : ℝ) ∂(N.marginal i))
        * ((renewalMeasure (N.marginal i) (Set.Ico 0 (S - s))).toReal - 1)
      ≤ ∫ x in Set.Ico 0 (S - s), N.F i (S - x) ∂(renewalMeasure (N.marginal i)) := by sorry
end OWMR
