-- Prove2me | Theorems.Thm_OWMR_fifo_retailer_comparison
-- name    : OWMR.fifo_retailer_comparison
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T01:17:36.193303+00:00
-- url     : https://prove2.me/theorems/b00dc0c9-f883-459a-8346-2d695b3dfdc6
-- title:
--   Retailer comparison: $\mathcal L_i\le(\gamma_m-1)J_i(5K_i/3)$
-- statement:
--   This is the retailer comparison in Step 1 of the proof of Theorem 1 (Section 5.4 of the source), which refines Proposition 1.
--
--   Consider an OWMR network that satisfies the standing assumptions, admissible choices for the FIFO policy $\pi_{\rm FIFO}$ of Definition 1, and a retailer $i$. Let $m\ge1$ and suppose $H_i\ge mh$ and $p\ge h$. Then the augmented cost $\mathcal L_i$ of the $(s,S)$ pair that retailer $i$ operates satisfies
--
--   $$\mathcal L_i\le\left(\frac54+\frac1{4m}\right)J_i\!\left(\frac{5K_i}3\right)=(\gamma_m-1)\,J_i\!\left(\frac{5K_i}3\right),\qquad\gamma_m=\frac94+\frac1{4m}.$$
--
--   Here $\mathcal L_i$ is the long-run average cost of that pair in retailer $i$'s single-location problem with actual setup cost $K_i$ plus its mirror cost, and $J_i(k)$ is the optimal average cost of that problem with setup cost $k$. For $K_i>0$, retailer $i$ operates the cheaper, in augmented cost, of a canonical optimum at planning setup cost $5K_i/3$ and its best half window; for $K_i=0$ it operates base stock at a minimizer of $F_i$.
--
--   With $m=1$ the factor is $3/2$, as in Proposition 1, and it falls toward $5/4$ as $m$ grows. This is the retailer part of the upper bound in Theorem 1.
--
--   **Formalization Note** The augmented cost is `N.augCost i (c.s i) (c.S i)`, and the factor enters through `ENNReal.ofReal`.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 5.4 (Assembly of the Guarantee), Step 1 of the proof of Theorem 1, eq. (32), p. 26; it refines Proposition 1 (Single-Location Comparison), p. 19.

import Definitions.Def_owmr_fifo_policy

open scoped ENNReal

namespace OWMR
theorem fifo_retailer_comparison {n : ℕ} (N : Network n) (hN : N.Standing)
    (m : ℝ) (hm : 1 ≤ m) (c : FIFOChoice n) (hc : IsFIFOChoice N c) (i : Fin n)
    (hH : m * N.h ≤ N.H i) (hp : N.h ≤ N.p) :
    N.augCost i (c.s i) (c.S i)
      ≤ ENNReal.ofReal (5 / 4 + 1 / (4 * m)) * N.J i (5 * N.K i / 3) := by sorry
end OWMR
