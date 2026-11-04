-- Prove2me | Theorems.Thm_LostSalesExpGap_ConstOrder_lemma_4
-- name    : LostSalesExpGap.ConstOrder.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:11:12.371505+00:00
-- url     : https://prove2.me/theorems/b4296520-b59f-4893-a09f-e8b32aec4b03
-- title:
--   Lemma 4, p. 12 — r∞ ≤ r_L for all L ≥ 1
-- statement:
--   In the lost-sales model with i.i.d. nonnegative demand of finite mean and strictly positive variance and costs $h,p>0$, let $r_\infty$ be the least minimizer of $C(\pi_r)$ on $[0,\mathbb E[D]]$ and, for $L\ge1$, $r_L$ the least minimizer of $C_L(r)=h\mathbb E[I^r_L]+p\mathbb E[D]-pr$ on $[0,\mathbb E[D]]$. Then
--   $$
--   r_\infty\le r_L\qquad\text{for all }L\ge1 .
--   $$
--
--   Since $C_L$ penalizes inventory less than $C(\pi_r)$, its optimal order is larger; the lemma is used to show that two terms of (6) nearly cancel.
--
--   **Formalization Note** $L$ here is any horizon $\ge1$, not tied to the model's lead time.
-- source:
--   Xin, Goldberg, Optimality gap of constant-order policies decays exponentially in the lead time for lost sales models, arXiv:1409.1499v2, Lemma 4, p. 12 (proof Sec. 5.4, pp. 20–21)

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LostSalesExpGap.ConstOrder

/-- Lemma 4, p. 12: `r∞ ≤ r_m` for all `m ≥ 1`. -/
theorem lemma_4 (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters)
    (hP : LostSalesConstantOrder.LargeLeadTime.NonDeterministic P) :
    ∀ m : ℕ, 1 ≤ m → rInf P c ≤ rL P c m := by sorry

end LostSalesExpGap.ConstOrder
