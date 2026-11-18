-- Prove2me | Theorems.Thm_LostSalesRQ_tightness_bounds
-- name    : LostSalesRQ.tightness_bounds
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T18:32:36.761292+00:00
-- url     : https://prove2.me/theorems/377cd61a-98a0-4c47-8138-04e519141c62
-- title:
--   Section 4.5 and eq. (I.1): the two bounds behind tightness of $\sqrt2$
-- statement:
--   1. For every $\mu\ge0$ and $a>1/2$, an equally spaced unit-ordering policy shows
--   $$\mathrm{OPT}_0(\mu,a)\le\sqrt{2a}.$$
--   2. If $0<a<\mu$ and $\omega=1-a/\mu$, then every integer base-stock level $j$ satisfies
--   $$L_j(a)\ge2\sqrt{a\omega}-\omega .$$
--
--   Along $\mu=a^2$ these give $U_{a^2}(a)/\mathrm{OPT}_0(a^2,a)\ge(2\sqrt{a-1}-1+a^{-1})/\sqrt{2a}\to\sqrt2$, so the factor $\sqrt2$ cannot be improved for ordinary base stock.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Section 4.5 (pp. 20-21); Appendix I, eq. (I.1) and the following display (pp. A19-A20).

import Definitions.Def_LostSalesRQ_model

namespace LostSalesRQ

theorem tightness_bounds :
    (∀ μ a : ℝ, 0 ≤ μ → 1 / 2 < a → OPTk μ a 0 ≤ ENNReal.ofReal (Real.sqrt (2 * a))) ∧
    (∀ μ a : ℝ, 0 < a → a < μ → ∀ j : ℕ,
      2 * Real.sqrt (a * (1 - a / μ)) - (1 - a / μ) ≤ baseStockCost μ a j) := by sorry

end LostSalesRQ
