-- Prove2me | Theorems.Thm_LostSalesLearning_ValueGap_lemmaB5_domination_alternates
-- name    : LostSalesLearning.ValueGap.lemmaB5_domination_alternates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T10:18:24.666777+00:00
-- url     : https://prove2.me/theorems/44329352-da4f-4fdc-9aea-28fe027d9708
-- title:
--   Lemma B.5, p. 21 — the two state trajectories alternate in ⪰ order at the crossing times of Definition B.4
-- statement:
--   Let $L\ge 1$ and let $\mathbf s_1,\mathbf s'_1\in\mathcal S^x$ with $\mathbf s'_1\succeq\mathbf s_1$. Run both chains on the same demand path. Define $\sigma_0=1$, let $\tau_{i+1}$ be the first later time with $I'_{\tau_{i+1}}<I_{\tau_{i+1}}$, and let $\sigma_{i+1}$ be the first time after $\tau_{i+1}$ with $I'_{\sigma_{i+1}}>I_{\sigma_{i+1}}$, whenever these times exist. Then, for every defined crossing time,
--   $$\mathbf s'_{\sigma_i}\succeq\mathbf s_{\sigma_i}\quad\text{and}\quad\mathbf s'_{\tau_{i+1}}\preceq\mathbf s_{\tau_{i+1}}.$$
--
--   This is Lemma B.5's full alternation conclusion along the crossing sequence of Definition B.4. The order changes at successive first crossings, which is used to bound the difference in total sales in Lemma B.6.
--
--   **Formalization Note** Time is 0-based, so the paper's $\sigma_0=1$ is Lean time `0`. `alternationTimes` constructs the first crossings; `none` means no later crossing exists. Once the two chains meet, later strict crossings cannot occur, which is how the paper's bound by its coalescence time $\Gamma$ is represented. Both chains use the same demand path, and $L\ge1$ is the standing assumption of Appendix B.
-- source:
--   Agrawal & Jia, Learning in Structured MDPs with Convex Cost Functions, arXiv:1905.04337v1, p. 21, Lemma B.5 and its proof (Definition B.4)

import Mathlib
import Definitions.Def_LostSalesLearning_ValueGap_Setting

open MeasureTheory
open scoped NNReal

namespace LostSalesLearning.ValueGap

theorem lemmaB5_domination_alternates {L : ℕ} (hL : 1 ≤ L) (x : ℝ) (s s' : Fin (L + 1) → ℝ)
    (hs : s ∈ Sx L x) (hs' : s' ∈ Sx L x) (hdom : Dominates s' s)
    (d : ℕ → ℝ≥0) :
    (∀ i σ, (alternationTimes s s' d i).1 = some σ →
      Dominates (traj s' d σ) (traj s d σ)) ∧
    (∀ i τ, (alternationTimes s s' d i).2 = some τ →
      Dominates (traj s d τ) (traj s' d τ)) := by sorry

end LostSalesLearning.ValueGap
