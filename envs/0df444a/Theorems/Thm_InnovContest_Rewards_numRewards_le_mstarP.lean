-- Prove2me | Theorems.Thm_InnovContest_Rewards_numRewards_le_mstarP
-- name    : InnovContest.Rewards.numRewards_le_mstarP
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-21T11:57:37.068834+00:00
-- url     : https://prove2.me/theorems/d92195fe-af77-495f-96cf-175abf8854af
-- title:
--   Proof of Theorem 2(ii) — optimal contests never use more than $m_p^*$ rewards
-- statement:
--   In the contest model of Theorem 2, let $0<c_p<B<n c_p$ and $c_f\ge0$. Every optimal allocation $r$ of the firm's problem (expected best submission minus $c_f$ times the probability that nobody enters, over all feasible allocations with budget $B$) has at most $m_p^*(B)$ strictly positive rewards,
--   $$m^*=\#\{j\le n: r_j>0\}\ \le\ m_p^*(B),$$
--   where $m_p^*(B)$ is the largest number $m$ of equal awards $B/m$ minimizing the entry threshold $a_{\min}$ (Theorem 1). This is the upper bound $m^*\le m_p^*$ of Theorem 2(ii); in the cases where the optimum is winner-take-all it holds since $m_p^*\ge1$.
-- source:
--   Stouras, Hutchison-Krupat & Chao, The Role of Participation in Innovation Contests, SSRN 2924224 (accepted version; Management Science 68(6) 2022, doi:10.1287/mnsc.2021.4111), p. 12, Theorem 2 (bound m* ≤ m_p^*); proof of Theorem 2, pp. 28–29

import Mathlib
import Definitions.Def_InnovContest_Rewards_Model

namespace InnovContest.Rewards

/-- Proof of Theorem 2(ii), pp. 28–29: an optimal allocation never uses more positive rewards
than the participation-maximizing number `m_p^*`. -/
theorem numRewards_le_mstarP (M : AbilityModel) (budget cp cf : ℝ)
    (hcp : 0 < cp) (hbudget : cp < budget)
    (hupper : budget < (M.n : ℝ) * cp) (hcf : 0 ≤ cf)
    (r : ℕ → ℝ) (hopt : IsOptimal M budget cp cf r) :
    numRewards M.n r ≤ mstarP M budget cp := by sorry

end InnovContest.Rewards
