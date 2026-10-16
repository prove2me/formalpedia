-- Prove2me | Theorems.Thm_NonstatRL_Oracle_eq24_all_windows
-- name    : NonstatRL.Oracle.eq24_all_windows
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T04:29:12.652841+00:00
-- url     : https://prove2.me/theorems/29f8b3d5-2eba-4bfc-ae03-05404eaf68b2
-- title:
--   (24), p. 34 — horizon bound for every integer window
-- statement:
--   Under the nonstationary MDP and common diameter assumptions, let $1\le W\le T$ be an integer window length. For every allowed history-dependent randomized policy and initial state,
--
--   $$\sum_{t=1}^{T}\rho_t^*\ge\mathbb E\!\left[\sum_{t=1}^{T}r_t(s_t,a_t)\right]-\frac{4TD_{\max}}{W}-2W(B_r+2D_{\max}B_p).$$
--
--   This is the last inequality of (24). It holds for every allowed window length and is the direct input to Proposition 1's choice of $W$.
--
--   **Formalization Note** The real division is safe because $W\ge1$. The budget sums stop at $T-1$, as (1) defines. Paper time starts at one, while Lean time starts at zero. The result uses the nonstationary trajectory law, nonempty state and action sets, and the diameter including return times.
-- source:
--   Cheung, Simchi-Levi & Zhu, Non-Stationary Reinforcement Learning: The Blessing of (More) Optimism, arXiv:1906.02922v4, p. 34, Appendix A.2, (24), final inequality

import Mathlib
import Definitions.Def_FiniteMDPLearning
import Definitions.Def_NonstatRL_Oracle_Model
import Definitions.Def_NonstatRL_Oracle_Trajectory

open BanditAlgorithm ENNReal MeasureTheory

namespace NonstatRL.Oracle

/-- Final inequality of (24), Appendix A.2, p. 34. -/
theorem eq24_all_windows {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (hS : 0 < S)
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ) (Dmax : ℝ)
    (hD : ∀ u, u < T → diameter (M u) As ≤ ENNReal.ofReal Dmax)
    (s₁ : Fin S) (π : MDPPolicy S A) (hπ : IsAllowedPolicy As π)
    (W : ℕ) (hW : 1 ≤ W) (hWT : W ≤ T) :
    expectedReward M s₁ π T - 4 * (T : ℝ) * Dmax / (W : ℝ) -
      2 * (W : ℝ) *
        (rewardBudget M As T + 2 * Dmax * transBudget M As T) ≤
      ∑ t ∈ Finset.range T, optGain (M t) As := by sorry

end NonstatRL.Oracle
