-- Prove2me | Theorems.Thm_LearnVsOpt_lagrangian_reduction
-- name    : LearnVsOpt.lagrangian_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:03:59.300001+00:00
-- url     : https://prove2.me/theorems/d1a98d6d-f5ca-4521-896f-d2323a8185c9
-- title:
--   Display after Lemma 7.1, p.23 — the Lagrangian bound for a budget-respecting sequence
-- statement:
--   Consider any sequence of pairs of actions $(i_1,j_1),\dots,(i_T,j_T)$ such that the optimizer's budget is observed, $\sum_tC_O[i_t,j_t]\le\rho_OT$, and let $\mu^\star\ge0$ minimize $\mu\mapsto\mathrm{BSE}_\mu$ over $\mu\ge0$. Then
--   $$
--   \sum_{t=1}^TU_O[i_t,j_t]-T\cdot\mathrm{BSE}_2\le\sum_{t=1}^T\big(U_O[i_t,j_t]-\mu^\star C_O[i_t,j_t]+\mu^\star\rho_O\big)-T\cdot\mathrm{BSE}_{\mu^\star}.
--   $$
--   The optimizer's benefit over its budgeted value is thus bounded by that of the Lagrangian optimizer over its own value.
--
--   Differences from the source:
--   - encoding: max in (2), (26), (27); both (2) and (26) are named BSE → sSup of the set of values, named BSE and BSE₂; reason: the sets are nonempty and bounded under the null actions; attainment is not a claim of the theorem
--   - encoding: a sequence of pairs of actions, μ⋆ from Lemma 7.1 → i, j : Fin T → …, and μ⋆ any minimizer over μ ≥ 0; reason: same objects
--   - encoding: the null actions of §2 and §7 → j₀ with C_L[i, j₀] = 0, and ∃ i, C_O[i, ·] = 0; reason: the paper's assumptions, as hypotheses
-- source:
--   Fikioris, Sivan & Tardos, Learning vs. Optimizing Players in Budgeted Games, arXiv:2611.05580, display after Lemma 7.1, p.23

import Mathlib
import Definitions.Def_LearnVsOpt_BSE

namespace LearnVsOpt

/-- **The Lagrangian reduction** (Fikioris, Sivan & Tardos, arXiv:2611.05580, display after Lemma 7.1,
p.23). For any sequence of pairs of actions `(i_1, j_1), …, (i_T, j_T)` such that the optimizer's budget
is observed, and `μ⋆` the minimizer of `μ ↦ BSE_μ` over `μ ≥ 0`,
`Σ_t U_O[i_t, j_t] − T·BSE ≤ Σ_t (U_O[i_t, j_t] − μ⋆C_O[i_t, j_t] + μ⋆ρ_O) − T·BSE_{μ⋆}`. -/
theorem lagrangian_reduction {nO nL : ℕ} (G : Game nO nL) (ρL ρO : ℝ) (hρL₀ : 0 < ρL) (hρL₁ : ρL ≤ 1)
    (hρO₀ : 0 < ρO) (hρO₁ : ρO ≤ 1) (j₀ : Fin nL) (hj₀ : ∀ i, G.CL i j₀ = 0)
    (hnull : ∃ i, ∀ j, G.CO i j = 0) (μS : ℝ) (hμ : 0 ≤ μS)
    (hmin : ∀ μ : ℝ, 0 ≤ μ → G.BSEmu ρL ρO μS ≤ G.BSEmu ρL ρO μ)
    (T : ℕ) (i : Fin T → Fin nO) (j : Fin T → Fin nL)
    (hbudget : ∑ t, G.CO (i t) (j t) ≤ ρO * T) :
    ∑ t, G.UO (i t) (j t) - T * G.BSE₂ ρL ρO ≤
      ∑ t, (G.UO (i t) (j t) - μS * G.CO (i t) (j t) + μS * ρO) - T * G.BSEmu ρL ρO μS := by sorry

end LearnVsOpt
