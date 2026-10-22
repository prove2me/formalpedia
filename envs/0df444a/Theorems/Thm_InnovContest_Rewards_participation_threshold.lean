-- Prove2me | Theorems.Thm_InnovContest_Rewards_participation_threshold
-- name    : InnovContest.Rewards.participation_threshold
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-21T11:57:52.911983+00:00
-- url     : https://prove2.me/theorems/c48a6488-de5a-4e73-bb8b-a29ecbf83ab3
-- title:
--   Theorem 2 — the budget threshold $\hat c_p$ for participation
-- statement:
--   In the contest model of Theorem 2, fix a participation cost $c_p>0$. There is a threshold $\hat c_p>c_p$ such that for every budget $c_p<B<n c_p$:
--
--   * if $B<\hat c_p$, winner-take-all attracts weakly more entry than any equal split: $a_{\min}(\text{WTA})\le a_{\min}(B/m\text{ to ranks }1..m)$ for all $1\le m\le n$ (so, by Theorem 1, it maximizes participation over all feasible allocations);
--   * if $B>\hat c_p$, the participation-maximizing equal split over $m_p^*(B)$ ranks has a strictly lower entry threshold than winner-take-all.
--
--   The key fact is that the set of budgets at which winner-take-all is participation-maximal among equal splits is an initial segment of $(c_p,nc_p)$: it contains $(c_p,2c_p)$ (no split with $m\ge2$ attracts anyone), and it is closed downward because $\mathrm{ordCDF}_{n-1}(n-m,q)/q^{n-1}$ is nonincreasing in $q$.
-- source:
--   Stouras, Hutchison-Krupat & Chao, The Role of Participation in Innovation Contests, SSRN 2924224 (accepted version; Management Science 68(6) 2022, doi:10.1287/mnsc.2021.4111), p. 12, Theorem 2 (threshold ĉ_p); proof of Theorem 2, pp. 28–29, with Theorem 1, p. 10

import Mathlib
import Definitions.Def_InnovContest_Rewards_Model

namespace InnovContest.Rewards

/-- The budget threshold `ĉ_p` of Theorem 2: below it winner-take-all maximizes participation
among equal splits, above it a multiple equal split strictly lowers the entry threshold. -/
theorem participation_threshold (M : AbilityModel) (cp : ℝ) (hcp : 0 < cp) :
    ∃ cpHat : ℝ, cp < cpHat ∧
      ∀ budget : ℝ, cp < budget → budget < (M.n : ℝ) * cp →
        (budget < cpHat → ∀ m ∈ Finset.Icc 1 M.n,
          amin M (equalSplit budget 1) cp ≤ amin M (equalSplit budget m) cp) ∧
        (cpHat < budget →
          amin M (equalSplit budget (mstarP M budget cp)) cp <
            amin M (equalSplit budget 1) cp) := by sorry

end InnovContest.Rewards
