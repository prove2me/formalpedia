-- Prove2me | Theorems.Thm_LostSalesLearning_ValueGap_lemmaB6_total_sales_gap
-- name    : LostSalesLearning.ValueGap.lemmaB6_total_sales_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T10:18:23.864315+00:00
-- url     : https://prove2.me/theorems/2255aa0f-feed-45ac-bc05-5eb25f7df49e
-- title:
--   Lemma B.6, p. 21 — if s′_1 ⪰ s_1 in S^x then |n^x_T(s′_1) − n^x_T(s_1)| ≤ 3x
-- statement:
--   Let $L\ge 1$ and let $\mathbf s_1,\mathbf s'_1\in\mathcal S^x$ with $\mathbf s'_1\succeq\mathbf s_1$. Run the two base-stock lost-sales chains on the same demand path $d_1,d_2,\dots\ge 0$, and let $n^x_T(\mathbf s)=\sum_{t=1}^{T}y_t$ be the total sales over $T$ periods from the start state $\mathbf s$. Then for every horizon $T$,
--   $$\big|n^x_T(\mathbf s'_1)-n^x_T(\mathbf s_1)\big|\le 3x .$$
--
--   The bound does not grow with $T$ or with the lead time $L$: the two chains alternate between $\mathbf s'_t\succeq\mathbf s_t$ and $\mathbf s'_t\preceq\mathbf s_t$ in cycles, and the sales differences of successive cycles compensate. Together with Lemma B.7 it bounds the difference of values in Lemma 2.5.
--
--   **Formalization Note** Total sales are computed along one demand path, the same for both start states, and the statement holds for every path. The hypothesis $L\ge 1$ is the standing assumption of Appendix B.
-- source:
--   Agrawal & Jia, Learning in Structured MDPs with Convex Cost Functions, arXiv:1905.04337v1, p. 21, Lemma B.6; proof pp. 21–22

import Mathlib
import Definitions.Def_LostSalesLearning_ValueGap_Setting

open MeasureTheory
open scoped NNReal

namespace LostSalesLearning.ValueGap

theorem lemmaB6_total_sales_gap {L : ℕ} (hL : 1 ≤ L) (x : ℝ) (s s' : Fin (L + 1) → ℝ)
    (hs : s ∈ Sx L x) (hs' : s' ∈ Sx L x) (hdom : Dominates s' s) (d : ℕ → ℝ≥0)
    (T : ℕ) :
    |totalSales s' d T - totalSales s d T| ≤ 3 * x := by sorry

end LostSalesLearning.ValueGap
