-- Prove2me | Theorems.Thm_LostSalesExpGap_ConstOrder_opt_ge_CL
-- name    : LostSalesExpGap.ConstOrder.opt_ge_CL
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-05T08:11:31.874273+00:00
-- url     : https://prove2.me/theorems/6414bf13-09ad-44e5-b38f-3ee34eb9e451
-- title:
--   Lemma 2 (first claim), p. 11 — OPT(L) ≥ C_L(r_L)
-- statement:
--   Consider the periodic-review lost-sales inventory model with i.i.d. nonnegative demands $D_1,D_2,\dots$ (finite positive mean, not a point mass), lead time $L\ge1$, holding cost $h>0$ and lost-sales penalty $p>0$, started empty. Let $\mathrm{OPT}(L)$ be the infimum of the long-run average cost $C(\pi)$ over all admissible policies. For $r\in[0,\mathbb E[D]]$ put
--   $$I^r_L=\max_{0\le j\le L}\Big(jr-\sum_{i=1}^jD_i\Big),\qquad C_L(r)=h\,\mathbb E[I^r_L]+p\,\mathbb E[D]-p\,r,$$
--   and let $r_L$ be the infimum of the set of minimisers of $C_L$ over $[0,\mathbb E[D]]$. Then
--   $$\mathrm{OPT}(L)\ \ge\ C_L(r_L).$$
--
--   This is the first assertion of Lemma 2 of Xin and Goldberg, the lower bound on the optimal cost that, combined with formula (3) for the constant-order cost, yields the decomposition (5) of the optimality gap. In the paper it follows from Theorem 2 (the stationary inventory and pipeline of an optimal policy) together with the convexity/Jensen argument of Observation 1.
--
--   **Formalization Note.** The model is the published `CappedBaseStock` model (zero-based time, empty initial state, costs in $[0,\infty]$); $\mathrm{OPT}(L)$ ranges over all measurable history-dependent randomised policies, a class containing the paper's Markov class, so the bound is at least as strong as printed. $C_L$ and $r_L$ are `CL` and `rL` of the published `LostSalesExpGap_ConstOrder_ConstantOrder` definitions, and the real number $C_L(r_L)$ is embedded in $[0,\infty]$ via `ENNReal.ofReal`.
-- source:
--   Xin, Goldberg, Optimality gap of constant-order policies decays exponentially in the lead time for lost sales models, arXiv:1409.1499v2, Lemma 2 (first claim), p. 11

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LostSalesExpGap.ConstOrder

/-- Lemma 2, first claim, p. 11: `OPT(L) ≥ C_L(r_L)`, where `C_L(r) = h E[I^r_L] + p E[D] − p r`
and `r_L` is the least minimiser of `C_L` over `[0, E[D]]`. `OPT(L)` is the infimum of the long-run
average cost over all admissible policies, in `[0, ∞]`. -/
theorem opt_ge_CL (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters)
    (hP : LostSalesConstantOrder.LargeLeadTime.NonDeterministic P) :
    ENNReal.ofReal (CL P c (rL P c c.L) c.L) ≤ CappedBaseStock.OPT P c := by sorry

end LostSalesExpGap.ConstOrder
