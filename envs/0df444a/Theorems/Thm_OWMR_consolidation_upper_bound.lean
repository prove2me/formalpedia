-- Prove2me | Theorems.Thm_OWMR_consolidation_upper_bound
-- name    : OWMR.consolidation_upper_bound
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T01:38:09.586018+00:00
-- url     : https://prove2.me/theorems/8aca20eb-d006-4ed0-9e36-11f2f914f0b5
-- title:
--   Consolidation upper bound: $C(\pi^{(m)}_{\rm con})\le2J_0(g_mK_0)+B_m\sum_iJ_i(\zeta_mK_i)$
-- statement:
--   This is the cost bound for the consolidation policy that the source states after Theorem 2 (Section 6) and proves in Appendix C.
--
--   Let $m\ge1$, and set $g_m=\bar\gamma_m/2=13/6+16/(57m)$, $\zeta_m=g_m/(g_m-1)$, and $B_m=2(g_m-1)$. Consider an OWMR network that satisfies the standing assumptions, in which the retailer demands within each period are associated, $H_i\ge mh$ for every retailer, and $p\ge h$. Then from every valid initial state $x$, for arbitrary nonnegative setup costs and all finite lead times, the deterministic consolidation policy $\pi^{(m)}_{\rm con}$ of Definition 2 satisfies
--
--   $$C(\pi^{(m)}_{\rm con})\le2J_0(g_mK_0)+B_m\sum_{i=1}^nJ_i(\zeta_mK_i),$$
--
--   where $C$ is the long-run average expected cost from $x$, and $J_0(k)$ and $J_i(k)$ are the optimal average costs of the supplier's and retailer $i$'s single-location problems with setup cost $k$.
--
--   The right side is twice the left side of the shared-cost lower bound (Proposition 3) at $\gamma=g_m$, so this bound and Proposition 3 give Theorem 2 with the factor $\bar\gamma_m=2g_m$.
--
--   **Formalization Note** $g_m$, $\zeta_m$, and $B_m$ are `conG m`, `conZeta m`, and `conB m`; costs are extended nonnegative reals.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 6, display following Theorem 2 (p. 28); proved in Appendix C as eq. (C.28) (p. E.20) for the uniform-offset policy and transferred to the consolidation policy in Steps 7 and 8 (Sections C.7 and C.8, pp. E.20-E.21).

import Definitions.Def_owmr_consolidation_policy

open scoped ENNReal

namespace OWMR
theorem consolidation_upper_bound {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing)
    (hA : N.Associated) (m : ℝ) (hm : 1 ≤ m) (hH : ∀ i, m * N.h ≤ N.H i) (hp : N.h ≤ N.p)
    (x : InitState n) (hx : x.Valid) (c : ConChoice n) (hc : IsConChoice N m c) :
    (conPolicy N x c).avgCost N x
      ≤ 2 * N.J0 (conG m * N.K0) + ENNReal.ofReal (conB m) * ∑ i, N.J i (conZeta m * N.K i) := by sorry
end OWMR
