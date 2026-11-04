-- Prove2me | Theorems.Thm_LostSalesExpGap_ConstOrder_eq_3
-- name    : LostSalesExpGap.ConstOrder.eq_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:10:30.325278+00:00
-- url     : https://prove2.me/theorems/92e8bea8-4699-4ee0-b44c-09c1c261fc8e
-- title:
--   Eq. (3), p. 6 — C(π_r) = hE[I^r_∞] + pE[D] − pr for r ∈ [0, E[D])
-- statement:
--   Let $D_1,D_2,\dots$ be i.i.d. nonnegative demands with finite mean $\mathbb E[D]$, let $L\ge1$ be the lead time and $h,p>0$ the holding and lost-sales costs. For $r\ge0$ let $\pi_r$ be the policy that orders $r$ in every period, started from the empty state, and $C(\pi_r)$ its long-run average cost. Let $I^r_\infty=\sup_{j\ge0}\big(jr-\sum_{i=1}^jD_i\big)$. Then for every $r\in[0,\mathbb E[D])$,
--   $$
--   C(\pi_r)=h\,\mathbb E\Big[\sup_{j\ge0}\Big(jr-\sum_{i=1}^jD_i\Big)\Big]+p\,\mathbb E[D]-p\,r,
--   $$
--   independent of the lead time $L$.
--
--   This identity turns the search for the best constant-order policy into a one-dimensional problem about a random walk.
--
--   **Formalization Note** Both sides are in $[0,\infty]$; $p\,\mathbb E[D]-p\,r$ is written $p(\mathbb E[D]-r)\ge0$. The right-hand side does not mention $L$. No positive-variance assumption is needed.
-- source:
--   Xin, Goldberg, Optimality gap of constant-order policies decays exponentially in the lead time for lost sales models, arXiv:1409.1499v2, Sec. 2.2, eq. (3), p. 6

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LostSalesExpGap.ConstOrder

/-- Eq. (3), p. 6: for `r ∈ [0, E[D])`, `C(π_r) = h E[I^r_∞] + p E[D] − p r`, independent of the
lead time. `p E[D] − p r` is written `p (E[D] − r) ≥ 0`. -/
theorem eq_3 (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters) (r : ℝ)
    (hr₀ : 0 ≤ r) (hr : r < CappedBaseStock.mean P) :
    constCost P c r =
      ENNReal.ofReal c.h * EIinf P r + ENNReal.ofReal (c.p * (CappedBaseStock.mean P - r)) := by sorry

end LostSalesExpGap.ConstOrder
