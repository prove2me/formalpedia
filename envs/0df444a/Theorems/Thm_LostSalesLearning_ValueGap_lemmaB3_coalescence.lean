-- Prove2me | Theorems.Thm_LostSalesLearning_ValueGap_lemmaB3_coalescence
-- name    : LostSalesLearning.ValueGap.lemmaB3_coalescence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T10:17:56.730555+00:00
-- url     : https://prove2.me/theorems/c0ab0828-124e-489f-adc7-70c98747c6d2
-- title:
--   Lemma B.3, p. 20 — if I′_t ≥ I_t for t = 1, …, L + 1 then n_T(s′_{L+1}) = n_T(s_{L+1}) for any T
-- statement:
--   Let $L\ge 1$ and let $\mathbf s_1,\mathbf s'_1\in\mathcal S^x$ with $\mathbf s'_1\succeq\mathbf s_1$. Run the two base-stock chains on the same demand path, and let $I_t=s_t(0)$ and $I'_t=s'_t(0)$ be their on-hand inventories in period $t$. If
--   $$I'_t\ge I_t\qquad\text{for all } t\in\{1,2,\dots,L+1\},$$
--   then for every horizon $T$ the two chains restarted from their period-$(L+1)$ states $\mathbf s'_{L+1}$ and $\mathbf s_{L+1}$ have the same total sales over the next $T$ periods (driven by the remaining demands $d_{L+1},d_{L+2},\dots$):
--   $$n_T(\mathbf s'_{L+1})=n_T(\mathbf s_{L+1}).$$
--
--   The lemma says that if the chain started higher in the pipeline keeps at least as much on hand for $L+1$ consecutive periods, the two chains have coalesced: from then on they sell exactly the same amounts. It is the reason the alternation times of Definition B.4 are at most $L+1$ apart.
--
--   **Formalization Note** Time is 0-based: periods $1,\dots,L+1$ are `t < L + 1`, and $\mathbf s_{L+1}$ is `traj s d L`. The quantity $n_T(\mathbf s_{L+1})$ is the total sales of the chain started at `traj s d L` under the shifted demand path `fun t => d (L + t)`. Both chains use the same demand path. The hypothesis $L\ge 1$ is the standing assumption of Appendix B.
-- source:
--   Agrawal & Jia, Learning in Structured MDPs with Convex Cost Functions, arXiv:1905.04337v1, p. 20, Lemma B.3

import Mathlib
import Definitions.Def_LostSalesLearning_ValueGap_Setting

open MeasureTheory
open scoped NNReal

namespace LostSalesLearning.ValueGap

theorem lemmaB3_coalescence {L : ℕ} (hL : 1 ≤ L) (x : ℝ) (s s' : Fin (L + 1) → ℝ)
    (hs : s ∈ Sx L x) (hs' : s' ∈ Sx L x) (hdom : Dominates s' s) (d : ℕ → ℝ≥0)
    (hI : ∀ t < L + 1, onHand s d t ≤ onHand s' d t) :
    ∀ T : ℕ, totalSales (traj s' d L) (fun t => d (L + t)) T =
      totalSales (traj s d L) (fun t => d (L + t)) T := by sorry

end LostSalesLearning.ValueGap
