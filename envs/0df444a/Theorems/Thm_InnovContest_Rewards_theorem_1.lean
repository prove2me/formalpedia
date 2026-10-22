-- Prove2me | Theorems.Thm_InnovContest_Rewards_theorem_1
-- name    : InnovContest.Rewards.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:06.608016+00:00
-- url     : https://prove2.me/theorems/39403368-c4d0-4816-8ad5-30de2560d54b
-- title:
--   Theorem 1 — equal awards maximize participation
-- statement:
--   Let $c_p>0$ and $c_p<B<n c_p$. Among all feasible allocations with budget $B$, an equal split among some $m$ awards maximizes the probability of entry. If $m_p^*$ is the largest number of equal awards attaining this maximum, then $1\le m_p^*<n$, its equal split is feasible, and
--
--   $$a_{\min}(r^{(m_p^*)})\le a_{\min}(r')\quad\text{for every feasible allocation }r'.$$
--
--   The result identifies the participation side of the firm's performance versus entry tradeoff.
-- source:
--   Stouras, Hutchison-Krupat & Chao, The Role of Participation in Innovation Contests, SSRN 2924224 (accepted version), p. 10, Theorem 1; proof pp. 24–27

import Mathlib
import Definitions.Def_InnovContest_Rewards_Model

namespace InnovContest.Rewards

/-- Theorem 1, p. 10: an equal split maximizes entry probability over all allocations. -/
theorem theorem_1 (M : AbilityModel) (budget cp : ℝ)
    (hcp : 0 < cp) (hbudget : cp < budget)
    (hupper : budget < (M.n : ℝ) * cp) :
    1 ≤ mstarP M budget cp ∧ mstarP M budget cp < M.n ∧
    Feasible M.n budget (equalSplit budget (mstarP M budget cp)) ∧
    ∀ r : ℕ → ℝ, Feasible M.n budget r →
      amin M (equalSplit budget (mstarP M budget cp)) cp ≤ amin M r cp := by sorry

end InnovContest.Rewards
