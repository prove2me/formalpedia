-- Prove2me | Theorems.Thm_NonstatRL_Oracle_proposition1_oracle_gap
-- name    : NonstatRL.Oracle.proposition1_oracle_gap
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T04:29:13.310551+00:00
-- url     : https://prove2.me/theorems/f8c25ce4-1b28-4750-a51f-bc827a535364
-- title:
--   Proposition 1, p. 8 — oracle sum bounds every policy’s expected reward
-- statement:
--   Consider a horizon of $T$ rounds of a nonstationary finite MDP. Each state has an available action, each stationary MDP has diameter at most $D_{\max}$, and $B_r,B_p$ are the reward and transition variation budgets of (1). Put $B=B_r+2D_{\max}B_p$. Assume the paper's $0<B\le T$ and the additional condition $BT\ge1$. Then for every initial state and every allowed non-anticipatory policy,
--
--   $$\sum_{t=1}^{T}\rho_t^*\ge\mathbb E\!\left[\sum_{t=1}^{T}r_t(s_t,a_t)\right]-4(D_{\max}+1)\sqrt{BT}.$$
--
--   Thus the sum of stationary optimal gains bounds the best achievable expected cumulative reward, up to the stated drift term. The expectation integrates mean rewards under time-dependent transitions.
--
--   **Formalization Note** The extra condition $BT\ge1$ repairs a small-budget counterexample to the printed Proposition 1: with two states, one action per state, a slowly returning second state, $T=2$ and $B_r=10^{-12}$, the printed right side is close to $1$ while the oracle sum is about $2/11$. The proof's window selection needs an integer $W\le T$ in $[\sqrt{T/B},2\sqrt{T/B}]$, which requires this lower bound. Paper time $t$ is Lean index $t-1$. Policies are randomized kernels on state–action histories; conditioning a reward-aware policy on that history produces the same trajectory law. The state set and every allowed-action set are nonempty. The gain is exactly the occupancy-LP value, and the diameter is an extended nonnegative value that includes return times.
-- source:
--   Cheung, Simchi-Levi & Zhu, Non-Stationary Reinforcement Learning: The Blessing of (More) Optimism, arXiv:1906.02922v4, p. 8, Proposition 1; proof pp. 33–35, Appendix A.2

import Mathlib
import Definitions.Def_FiniteMDPLearning
import Definitions.Def_NonstatRL_Oracle_Model
import Definitions.Def_NonstatRL_Oracle_Trajectory

open BanditAlgorithm ENNReal MeasureTheory

namespace NonstatRL.Oracle

/-- Proposition 1, p. 8, with the necessary small-budget pin BT ≥ 1. -/
theorem proposition1_oracle_gap {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (hS : 0 < S)
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ) (Dmax : ℝ)
    (hD : ∀ u, u < T → diameter (M u) As ≤ ENNReal.ofReal Dmax)
    (hBudget : rewardBudget M As T + 2 * Dmax * transBudget M As T ≤ (T : ℝ))
    (hPos : 0 < rewardBudget M As T + 2 * Dmax * transBudget M As T)
    (hPin : 1 ≤ (rewardBudget M As T + 2 * Dmax * transBudget M As T) * (T : ℝ))
    (s₁ : Fin S) (π : MDPPolicy S A) (hπ : IsAllowedPolicy As π) :
    expectedReward M s₁ π T -
      4 * (Dmax + 1) *
        Real.sqrt ((rewardBudget M As T + 2 * Dmax * transBudget M As T) * T) ≤
      ∑ t ∈ Finset.range T, optGain (M t) As := by sorry

end NonstatRL.Oracle
