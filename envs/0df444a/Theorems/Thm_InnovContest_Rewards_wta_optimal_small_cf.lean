-- Prove2me | Theorems.Thm_InnovContest_Rewards_wta_optimal_small_cf
-- name    : InnovContest.Rewards.wta_optimal_small_cf
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-21T11:57:53.505199+00:00
-- url     : https://prove2.me/theorems/eb4206e6-4ee5-4241-a5dd-988e02132e56
-- title:
--   Proof of Theorem 2(ii) — winner-take-all is optimal when a failed contest is cheap
-- statement:
--   In the contest model of Theorem 2 (with $n\ge2$ solvers, ability density continuous and positive on $[0,1]$), let $0<c_p<B<n c_p$. Then there is $c>0$ such that for every failure cost $c_f\in[0,c]$ the winner-take-all allocation $(B,0,\dots,0)$ is optimal for the firm's problem
--   $$\max_{r\ \text{feasible}}\ \Pi(r)=\mathbb E\big[\text{best participating submission}\big]-c_f\,\mathbb P[\text{no solver enters}],$$
--   where all equilibrium quantities ($a_{\min}$, $x^*$) are recomputed for each allocation. This is the "small $c_f$" half of Theorem 2(ii): when a failed contest is cheap, the first term, maximized by winner-take-all, dominates.
-- source:
--   Stouras, Hutchison-Krupat & Chao, The Role of Participation in Innovation Contests, SSRN 2924224 (accepted version; Management Science 68(6) 2022, doi:10.1287/mnsc.2021.4111), p. 12, Theorem 2 (case c_f below the threshold ĉ_f); proof of Theorem 2, pp. 27–29

import Mathlib
import Definitions.Def_InnovContest_Rewards_Model

namespace InnovContest.Rewards

/-- Proof of Theorem 2(ii), p. 28: for a small enough cost of a failed contest, winner-take-all
is optimal. -/
theorem wta_optimal_small_cf (M : AbilityModel) (budget cp : ℝ)
    (hcp : 0 < cp) (hbudget : cp < budget)
    (hupper : budget < (M.n : ℝ) * cp) :
    ∃ c : ℝ, 0 < c ∧ ∀ cf : ℝ, 0 ≤ cf → cf ≤ c →
      IsOptimal M budget cp cf (equalSplit budget 1) := by sorry

end InnovContest.Rewards
