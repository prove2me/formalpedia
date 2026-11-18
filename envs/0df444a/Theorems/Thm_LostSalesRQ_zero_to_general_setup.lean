-- Prove2me | Theorems.Thm_LostSalesRQ_zero_to_general_setup
-- name    : LostSalesRQ.zero_to_general_setup
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T18:33:32.39489+00:00
-- url     : https://prove2.me/theorems/14ce7689-5a1c-4794-a0e3-c62b3e03b472
-- title:
--   Proposition 3: from zero to general setup cost
-- statement:
--   Fix $\mu\ge0$, $a\ge0$, $k\ge0$ and $c>0$. If the zero-setup comparison
--   $$U_\mu(a)\le c\,\mathrm{OPT}_0(\mu,a)$$
--   holds, then on every demand environment of rate one the classical family satisfies
--   $$C_{\rm rQ}(\mu,a,k)=\inf_{\pi\in\Pi_{\rm rQ}}C_{\mu,a,k}(\pi)\le R\,\mathrm{OPT}_k(\mu,a),\qquad R=\frac{c+\sqrt{c^2+4}}{2}.$$
--
--   With $c=\sqrt2$ this gives $R=(\sqrt2+\sqrt6)/2<1.932$. No division by $a$, $k$ or $\mathrm{OPT}_0(\mu,a)$ is involved, so the zero boundaries are included.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Proposition 3, eq. (27) (p. 23).

import Definitions.Def_LostSalesRQ_model

namespace LostSalesRQ

theorem zero_to_general_setup (μ a k c : ℝ) (hμ : 0 ≤ μ) (ha : 0 ≤ a) (hk : 0 ≤ k) (hc : 0 < c)
    (hprem : ENNReal.ofReal (minBaseStockCost μ a) ≤ ENNReal.ofReal c * OPTk μ a 0)
    (S : DemandSpace 1) :
    rQFamilyCost S μ 1 a k ≤
      ENNReal.ofReal ((c + Real.sqrt (c ^ 2 + 4)) / 2) * OPTk μ a k := by sorry

end LostSalesRQ
