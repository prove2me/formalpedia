-- Prove2me | Theorems.Thm_InnovContest_Rewards_rank_identity
-- name    : InnovContest.Rewards.rank_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:32.943481+00:00
-- url     : https://prove2.me/theorems/bf5bd922-c7bc-4fa6-9081-29fc8c9dd562
-- title:
--   Equation (EC.3) — probability of a performance rank
-- statement:
--   Let $n\ge2$, let $1\le j\le n$, and let $q\in[0,1]$ be a common ability CDF value. The probability that one solver ranks $j$th highest among $n$ independent solvers is
--
--   $$F_{n-j:n-1}(q)-F_{n-j+1:n-1}(q)=\binom{n-1}{j-1}q^{n-j}(1-q)^{j-1}.$$
--
--   This identity connects rank rewards to order statistics and is used in the threshold equation.
-- source:
--   Stouras, Hutchison-Krupat & Chao, The Role of Participation in Innovation Contests, SSRN 2924224 (accepted version), p. ec1 (PDF 35), equation (EC.3)

import Mathlib
import Definitions.Def_InnovContest_Rewards_OrderStats

namespace InnovContest.Rewards

/-- Equation (EC.3), p. ec1 (PDF 35): the probability of rank `j` from order-statistic CDFs. -/
theorem rank_identity (n j : ℕ) (hn : 2 ≤ n) (hj1 : 1 ≤ j) (hjn : j ≤ n)
    (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    ordCDF (n - 1) (n - j) q - ordCDF (n - 1) (n - j + 1) q =
      ((n - 1).choose (j - 1) : ℝ) * q ^ (n - j) * (1 - q) ^ (j - 1) := by sorry

end InnovContest.Rewards
