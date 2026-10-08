-- Prove2me | Theorems.Thm_LostSalesLearning_ValueGap_lemmaB7_total_onhand_gap
-- name    : LostSalesLearning.ValueGap.lemmaB7_total_onhand_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T10:18:39.413186+00:00
-- url     : https://prove2.me/theorems/7f6606fd-f69a-4c73-a7b6-20a6908e3043
-- title:
--   Lemma B.7, p. 23 — if s′ ⪰ s in S^x then |m^x_T(s) − m^x_T(s′)| ≤ 6Lx
-- statement:
--   Let $L\ge 1$ and let $\mathbf s,\mathbf s'\in\mathcal S^x$ with $\mathbf s'\succeq\mathbf s$. Run the two base-stock lost-sales chains on the same demand path $d_1,d_2,\dots\ge 0$, and let $m^x_T(\mathbf s)=\sum_{t=1}^{T}I_t$ be the total on-hand inventory over $T$ periods from the start state $\mathbf s$. Then for every horizon $T$,
--   $$\big|m^x_T(\mathbf s)-m^x_T(\mathbf s')\big|\le 6Lx .$$
--
--   The difference in cumulative on-hand inventory is linear in the lead time and does not grow with $T$. This, with Lemma B.6, is what makes the bound of Lemma 2.5 linear rather than exponential in $L$.
--
--   **Formalization Note** Total on-hand inventory is computed along one demand path, the same for both start states, and the statement holds for every path. The hypothesis $L\ge 1$ is the standing assumption of Appendix B.
-- source:
--   Agrawal & Jia, Learning in Structured MDPs with Convex Cost Functions, arXiv:1905.04337v1, p. 23, Lemma B.7; proof pp. 23–24

import Mathlib
import Definitions.Def_LostSalesLearning_ValueGap_Setting

open MeasureTheory
open scoped NNReal

namespace LostSalesLearning.ValueGap

theorem lemmaB7_total_onhand_gap {L : ℕ} (hL : 1 ≤ L) (x : ℝ) (s s' : Fin (L + 1) → ℝ)
    (hs : s ∈ Sx L x) (hs' : s' ∈ Sx L x) (hdom : Dominates s' s) (d : ℕ → ℝ≥0)
    (T : ℕ) :
    |totalOnHand s d T - totalOnHand s' d T| ≤ 6 * (L : ℝ) * x := by sorry

end LostSalesLearning.ValueGap
