-- Prove2me | Theorems.Thm_LostSalesExpGap_ConstOrder_chernoff_step
-- name    : LostSalesExpGap.ConstOrder.chernoff_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T22:11:41.84518+00:00
-- url     : https://prove2.me/theorems/3c59d75c-340f-4589-b1a6-37b4bec03fb7
-- title:
--   Sec. 3, p. 13 — Chernoff: ℙ(nr∞ ≥ Σ_{i≤n} D_i) ≤ γ^n
-- statement:
--   Let $D_1,D_2,\dots$ be i.i.d. nonnegative demands with finite mean, let $r_\infty$ be the best constant order and $\gamma=\inf_{\theta\ge0}e^{\theta r_\infty}\mathbb E[e^{-\theta D}]$. Then for every $n\ge1$,
--   $$
--   \mathbb P\Big(nr_\infty\ge\sum_{i=1}^nD_i\Big)\le\gamma^n .
--   $$
--
--   This is the large-deviation estimate that makes the optimality gap decay like $\gamma^{L+1}$.
--
--   **Formalization Note** No positive-variance assumption is needed for this bound.
-- source:
--   Xin, Goldberg, Optimality gap of constant-order policies decays exponentially in the lead time for lost sales models, arXiv:1409.1499v2, Sec. 3, proof of Theorem 1, p. 13 (Chernoff step)

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LostSalesExpGap.ConstOrder

/-- Sec. 3, p. 13 (proof of Theorem 1): by Chernoff's inequality,
`ℙ(n r∞ ≥ Σ_{i=1}^n D_i) ≤ γ^n` for every `n ≥ 1`. -/
theorem chernoff_step (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters) :
    ∀ n : ℕ, 1 ≤ n →
      CappedBaseStock.demandPathLaw P
          {d | ∑ i ∈ Finset.range n, (d i : ℝ) ≤ (n : ℝ) * rInf P c} ≤
        ENNReal.ofReal (gamma P c ^ n) := by sorry

end LostSalesExpGap.ConstOrder
