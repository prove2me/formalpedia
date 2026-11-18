-- Prove2me | Theorems.Thm_OWMR_fifo_candidate_comparison
-- name    : OWMR.fifo_candidate_comparison
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T01:38:03.870205+00:00
-- url     : https://prove2.me/theorems/747df92c-2fc4-409f-ba2c-438ddaee4457
-- title:
--   Two-candidate comparison: $\min\{\mathcal L_{\rm full},\mathcal L_{\rm half}\}\le J_i(5K_i/3)+\beta\hat w/2$
-- statement:
--   This is the two-candidate comparison of Proposition 1, in the sharper form that Step 1 of the proof of Theorem 1 uses.
--
--   Consider an OWMR network that satisfies the standing assumptions and a retailer $i$ with $H_i\ge h$, $p\ge h$, and setup cost $K_i>0$. Let $(\hat s,\hat S)$ be a canonical optimum of retailer $i$'s single-location problem at planning setup cost $5K_i/3$, with width $\hat w=\hat S-\hat s$, and let $(s',S')$ be a half window of $[\hat s,\hat S]$, of width $\hat w/2$, with the smallest average holding and backlog cost. Write $\mathcal L(s,S)$ for the augmented cost of the $(s,S)$ policy at the actual setup cost $K_i$: its long-run average cost in retailer $i$'s single-location problem plus its mirror cost. Then, with $\beta=hp/(h+p)$,
--
--   $$\min\{\mathcal L(\hat s,\hat S),\,\mathcal L(s',S')\}\le J_i\!\left(\frac{5K_i}3\right)+\frac{\beta\hat w}2.$$
--
--   Dividing by $G=J_i(5K_i/3)$, this reads $\min\{\mathcal L_{\rm full},\mathcal L_{\rm half}\}/G\le1+\omega/2$ with $\omega=\beta\hat w/G$. With $\beta\hat w\le G$ it gives the factor $3/2$ of Proposition 1, and with the canonical width bound it gives the retailer comparison in the proof of Theorem 1.
--
--   **Formalization Note** The augmented cost is `N.augCost`. The half window is given by `IsBestHalfWindow`, which selects the half window with the smallest average holding and backlog cost, equivalently the largest retained savings.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 4.6, Proposition 1 (Single-Location Comparison) and Steps 1-3 of its proof, eqs. (19)-(20), pp. 19-20, in the form min{L_full, L_half}/G <= 1 + omega/2 stated in Step 1 of the proof of Theorem 1 (Section 5.4, p. 26).

import Definitions.Def_owmr_single_location

open scoped ENNReal

namespace OWMR
theorem fifo_candidate_comparison {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n)
    (hH : N.h ≤ N.H i) (hp : N.h ≤ N.p) (hK : 0 < N.K i) (sh Sh s' S' : ℝ)
    (hcan : IsCanonicalOptimum (N.marginal i) (N.F i) (5 * N.K i / 3) sh Sh)
    (hhalf : IsBestHalfWindow (N.marginal i) (N.F i) sh Sh s' S') :
    min (N.augCost i sh Sh) (N.augCost i s' S')
      ≤ N.J i (5 * N.K i / 3) + ENNReal.ofReal (N.h * N.p / (N.h + N.p) * (Sh - sh) / 2) := by sorry
end OWMR
