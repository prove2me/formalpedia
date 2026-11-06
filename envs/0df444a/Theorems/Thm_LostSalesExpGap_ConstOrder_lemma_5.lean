-- Prove2me | Theorems.Thm_LostSalesExpGap_ConstOrder_lemma_5
-- name    : LostSalesExpGap.ConstOrder.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T22:10:25.412869+00:00
-- url     : https://prove2.me/theorems/fd2688b6-be5c-49b8-a918-ea57e2db054a
-- title:
--   Lemma 5, p. 12 — Σ_{n≥1} ℙ(nr∞ ≥ Σ_{i≤n} D_i) ≥ p/h
-- statement:
--   In the lost-sales model with i.i.d. nonnegative demand of finite mean and strictly positive variance and costs $h,p>0$, let $r_\infty$ be the best constant order. Then
--   $$
--   \sum_{n=1}^\infty\mathbb P\Big(nr_\infty\ge\sum_{i=1}^nD_i\Big)\ge\frac ph .
--   $$
--
--   This is a first-order optimality condition for $r_\infty$, and it lets the remaining terms of (6) be bounded by a geometric tail.
--
--   **Formalization Note** The series is taken in $[0,\infty]$, so a divergent series is $+\infty$ rather than a junk value. The summation index starts at $0$ in Lean (term $n$ is the paper's $n+1$).
-- source:
--   Xin, Goldberg, Optimality gap of constant-order policies decays exponentially in the lead time for lost sales models, arXiv:1409.1499v2, Lemma 5, p. 12 (proof Sec. 5.5, pp. 21–22)

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LostSalesExpGap.ConstOrder

/-- Lemma 5, p. 12: `Σ_{n=1}^∞ ℙ(n r∞ ≥ Σ_{i=1}^n D_i) ≥ p/h`, the series in `[0, ∞]` (the summand
at `n` is the paper's term `n + 1`). -/
theorem lemma_5 (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters)
    (hP : LostSalesConstantOrder.LargeLeadTime.NonDeterministic P) :
    ENNReal.ofReal (c.p / c.h) ≤
      ∑' n : ℕ, CappedBaseStock.demandPathLaw P
        {d | ∑ i ∈ Finset.range (n + 1), (d i : ℝ) ≤ ((n : ℝ) + 1) * rInf P c} := by sorry

end LostSalesExpGap.ConstOrder
