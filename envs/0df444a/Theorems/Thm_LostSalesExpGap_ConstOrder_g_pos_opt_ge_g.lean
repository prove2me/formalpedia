-- Prove2me | Theorems.Thm_LostSalesExpGap_ConstOrder_g_pos_opt_ge_g
-- name    : LostSalesExpGap.ConstOrder.g_pos_opt_ge_g
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:10:41.808979+00:00
-- url     : https://prove2.me/theorems/21011bb0-5dec-48ff-88d7-ff498204c860
-- title:
--   Sec. 2.3, p. 7 — g > 0 and OPT(L) ≥ g
-- statement:
--   In the lost-sales model (i.i.d. nonnegative demand $D$ with finite mean and strictly positive variance, lead time $L\ge1$, costs $h,p>0$, empty initial state), let
--   $$
--   g=\inf_{x\in\mathbb R}\mathbb E\big[h(x-D)^++p(x-D)^-\big]
--   $$
--   be the optimal single-period newsvendor cost. Then $g>0$ and $\mathrm{OPT}(L)\ge g$.
--
--   The lower bound $\mathrm{OPT}(L)\ge g$ converts the additive bound on $C(\pi_{r_\infty})-\mathrm{OPT}(L)$ into the ratio bound of Theorem 1.
--
--   **Formalization Note** $\mathrm{OPT}(L)$ is the infimum over all measurable history-dependent, possibly randomized policies, a class containing the paper's $\Pi$; the bound is therefore at least as strong as printed. It is compared with $g$ in $[0,\infty]$.
-- source:
--   Xin, Goldberg, Optimality gap of constant-order policies decays exponentially in the lead time for lost sales models, arXiv:1409.1499v2, Sec. 2.3, p. 7

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LostSalesExpGap.ConstOrder

/-- Sec. 2.3, p. 7: `g > 0` and `OPT(L) ≥ g`. -/
theorem g_pos_opt_ge_g (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters)
    (hP : LostSalesConstantOrder.LargeLeadTime.NonDeterministic P) :
    0 < gNV P c ∧ ENNReal.ofReal (gNV P c) ≤ CappedBaseStock.OPT P c := by sorry

end LostSalesExpGap.ConstOrder
