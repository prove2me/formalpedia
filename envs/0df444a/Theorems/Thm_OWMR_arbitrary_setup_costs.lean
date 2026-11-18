-- Prove2me | Theorems.Thm_OWMR_arbitrary_setup_costs
-- name    : OWMR.arbitrary_setup_costs
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T00:58:49.861364+00:00
-- url     : https://prove2.me/theorems/c47335ce-ee4a-4e0a-a89b-b71b9170152d
-- title:
--   Arbitrary setup costs: $C(\pi^{(m)}_{\rm con})\le\bar\gamma_m\,\mathrm{OPT}$ (Theorem 2)
-- statement:
--   Let $m\ge1$. Consider an OWMR network with $n\ge1$ retailers that satisfies the standing assumptions: demand vectors i.i.d. over periods with nonnegative components and $0<\mathbb E D_{i,t}<\infty$, setup costs $K_0,K_i\ge0$ (otherwise arbitrary), and $h,H_i,p>0$. Suppose
--
--   1. the retailer demands in each period are associated: $\operatorname{Cov}(u(D_t),v(D_t))\ge0$ for all bounded, measurable, coordinatewise nondecreasing $u,v$,
--   2. $H_i\ge mh$ for every retailer $i$, and
--   3. $p\ge h$.
--
--   Then, for all finite supplier and retailer lead times and from every valid initial state, the deterministic consolidation policy $\pi^{(m)}_{\rm con}$ of Definition 2 satisfies
--
--   $$C(\pi^{(m)}_{\rm con})\le\bar\gamma_m\,\mathrm{OPT},\qquad\bar\gamma_m=\frac{13}{3}+\frac{32}{57m}.$$
--
--   At $m=1$ the factor is $93/19<4.9$, and it decreases to $13/3$ as $m$ grows. Unlike Theorem 1, the factor does not depend on the ratio of retailer to supplier setup costs.
--
--   **Formalization Note** The conclusion holds for every admissible choice in Definition 2 (`IsConChoice N m c`); $\pi^{(m)}_{\rm con}$ depends on $m$ through these choices. Costs take values in $[0,\infty]$.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 6, Theorem 2 (Arbitrary Setup Costs), p. 28.

import Definitions.Def_owmr_consolidation_policy

open scoped ENNReal

namespace OWMR
theorem arbitrary_setup_costs {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing)
    (hA : N.Associated) (m : ℝ) (hm : 1 ≤ m) (hH : ∀ i, m * N.h ≤ N.H i) (hp : N.h ≤ N.p)
    (x : InitState n) (hx : x.Valid) (c : ConChoice n) (hc : IsConChoice N m c) :
    (conPolicy N x c).avgCost N x ≤ ENNReal.ofReal (13 / 3 + 32 / (57 * m)) * OPT N x := by sorry
end OWMR
