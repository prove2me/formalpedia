-- Prove2me | Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_eq_26
-- name    : LostSalesConstantOrder.LargeLeadTime.eq_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:20.53234+00:00
-- url     : https://prove2.me/theorems/9bb7b292-626b-4a1c-84cf-be88907e1ff5
-- title:
--   (26): $\mathbb P(i^r_\infty=k)\le(1-\Theta_r)^k$
-- statement:
--   Let $D_1,D_2,\dots$ be i.i.d. with law $\mathcal D$ (nonnegative, finite third moment, not deterministic), let $r\in[0,\mathbb E[D])$, and let $i^r_\infty$ be the largest index at which the walk $kr-\sum_{i=1}^kD_i$ attains its supremum. With $\Theta_r=(\mathbb E[D]-r)^2/(4(\mathbb E^2[D]+\mathbb E[D^2]))$, for every $k\ge0$,
--   $$
--   \mathbb P(i^r_\infty=k)\le(1-\Theta_r)^k.\tag{26}
--   $$
--
--   This geometric tail is the input of the bounds of Lemma 9.
--
--   **Formalization Note** $r=0$ is included.
-- source:
--   Goldberg, Katz-Rogozhnikov, Lu, Sharma & Squillante, Asymptotic Optimality of Constant-Order Policies for Lost Sales Inventory Models with Large Lead Times, arXiv:1211.4063v2, p. 17, §9.1, display (26) in the proof of Lemma 9

import Definitions.Def_LostSalesConstantOrder_LargeLeadTime_RandomWalk

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesConstantOrder.LargeLeadTime

/-- (26), §9.1, p. 17: for `r ∈ [0, E[D])` and every `k ≥ 0`, `P(i^r_∞ = k) ≤ (1 − Θ_r)^k`. -/
theorem eq_26 (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P)
    (r : ℝ≥0) (hr : (r : ℝ) < CappedBaseStock.mean P) (k : ℕ) :
    CappedBaseStock.demandPathLaw P {d | argmaxWalk r d = k} ≤
      ENNReal.ofReal ((1 - theta P r) ^ k) := by sorry

end LostSalesConstantOrder.LargeLeadTime
