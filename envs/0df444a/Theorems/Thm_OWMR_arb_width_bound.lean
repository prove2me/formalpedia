-- Prove2me | Theorems.Thm_OWMR_arb_width_bound
-- name    : OWMR.arb_width_bound
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T12:51:35.896343+00:00
-- url     : https://prove2.me/theorems/1e182df8-72ec-4109-8e2d-43d7ff6707a7
-- title:
--   Lemma C.5 (holding-rate width bound) for a canonical optimum
-- statement:
--   Fix retailer $i$ of a network under the standing assumptions, $m\ge1$ with $mh\le H_i$ and $h\le p$, a setup cost $k>0$, and a canonical optimum $(\hat s,\hat S)$ of $J_i(k)$. Let $w=\hat S-\hat s$, let $U$ be the renewal measure of the demand $D_i$ and $M=U[0,w)$, and let $\psi(u)=\max(1-4u/3,0)^2/(8/3)$. Then
--   $$\frac{h\int_{[0,w)}x\,U(dx)}{M}+\min\Bigl(\frac38hw,\ \frac{(h+p)w\int_{[0,w)}\psi(x/w)\,U(dx)}{M}\Bigr)\le\frac78\Bigl(1+\frac1m\Bigr)J_i(k)-\frac{7}{12m}\cdot\frac{k}{M}.$$
--   The first term is the average holding cost of the reserve that a full cycle leaves above $\hat s$; the minimum is the width cost of the reserve kept at the warehouse.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Appendix C, Step 5, Lemma C.5 with (C.21)-(C.23), pp. E.16-E.17.

import Definitions.Def_owmr_consolidation_policy
import Definitions.Def_owmr_renewal

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem arb_width_bound {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n) (m : ℝ)
    (hm : 1 ≤ m) (hH : m * N.h ≤ N.H i) (hp : N.h ≤ N.p) (k sh Sh : ℝ) (hk : 0 < k)
    (hc : IsCanonicalOptimum (N.marginal i) (N.F i) k sh Sh) :
    N.h * (∫ x in Set.Ico 0 (Sh - sh), x ∂(renewalMeasure (N.marginal i)))
        / (renewalMeasure (N.marginal i) (Set.Ico 0 (Sh - sh))).toReal
      + min (N.h * (3 / 8) * (Sh - sh))
          ((N.h + N.p) * (Sh - sh)
            * (∫ x in Set.Ico 0 (Sh - sh), max (1 - 4 * (x / (Sh - sh)) / 3) 0 ^ 2 / (8 / 3)
                ∂(renewalMeasure (N.marginal i)))
            / (renewalMeasure (N.marginal i) (Set.Ico 0 (Sh - sh))).toReal)
      ≤ 7 / 8 * (1 + 1 / m) * (N.J i k).toReal
        - 7 / (12 * m) * k / (renewalMeasure (N.marginal i) (Set.Ico 0 (Sh - sh))).toReal := by sorry
end OWMR
