-- Prove2me | Theorems.Thm_LostSalesLearning_ValueGap_lemmaB2_early_sales_gap
-- name    : LostSalesLearning.ValueGap.lemmaB2_early_sales_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T10:18:12.05303+00:00
-- url     : https://prove2.me/theorems/f503c3e4-f478-4fc8-81e6-c4cf75a9441c
-- title:
--   Lemma B.2, p. 20 — for t ≤ L + 1, Y′_t − Y_t ≤ max_{0≤k≤t−1}(δ_0 + … + δ_k) when s′_1 ⪰ s_1
-- statement:
--   Let $L\ge 1$ and let $\mathbf s_1,\mathbf s'_1\in\mathcal S^x$ be two starting states of the base-stock lost-sales chain with $\mathbf s'_1\succeq\mathbf s_1$, and write $\delta_i=s'_1(i)-s_1(i)$. Run both chains on one and the same demand path $d_1,d_2,\dots\ge 0$, and let $Y_t=\sum_{i=1}^{t}y_i$ and $Y'_t=\sum_{i=1}^{t}y'_i$ be the cumulative sales of the two chains up to period $t$. Then for every $t=1,2,\dots,L+1$,
--   $$Y'_t-Y_t\le\max_{0\le k\le t-1}\,(\delta_0+\delta_1+\dots+\delta_k).$$
--
--   During the first $L+1$ periods only the initial pipeline reaches the shelf, so the extra sales of the chain started higher in the pipeline are bounded by the largest partial sum of the initial difference. The lemma is the basic comparison step of the bound on total sales (Lemma B.6).
--
--   **Formalization Note** Time is 0-based, so $Y_t$ is the sum over `Finset.range t` and the maximum over $0\le k\le t-1$ is `Finset.sup'` over `Finset.range t`. Both chains are driven by the same demand path `d`; the paper compares them period by period under one demand. The hypothesis $L\ge 1$ is the standing assumption of Appendix B.
-- source:
--   Agrawal & Jia, Learning in Structured MDPs with Convex Cost Functions, arXiv:1905.04337v1, p. 20, Lemma B.2

import Mathlib
import Definitions.Def_LostSalesLearning_ValueGap_Setting

open MeasureTheory
open scoped NNReal

namespace LostSalesLearning.ValueGap

theorem lemmaB2_early_sales_gap {L : ℕ} (hL : 1 ≤ L) (x : ℝ) (s s' : Fin (L + 1) → ℝ)
    (hs : s ∈ Sx L x) (hs' : s' ∈ Sx L x) (hdom : Dominates s' s) (d : ℕ → ℝ≥0)
    (t : ℕ) (ht1 : 1 ≤ t) (ht2 : t ≤ L + 1) :
    ∑ i ∈ Finset.range t, sales s' d i - ∑ i ∈ Finset.range t, sales s d i ≤
      (Finset.range t).sup' ⟨0, Finset.mem_range.2 (by omega)⟩
        (fun k => ∑ j ∈ Finset.univ.filter (fun j : Fin (L + 1) => (j : ℕ) ≤ k), (s' j - s j)) := by sorry

end LostSalesLearning.ValueGap
