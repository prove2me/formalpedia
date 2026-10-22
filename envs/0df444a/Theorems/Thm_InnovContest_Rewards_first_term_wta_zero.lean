-- Prove2me | Theorems.Thm_InnovContest_Rewards_first_term_wta_zero
-- name    : InnovContest.Rewards.first_term_wta_zero
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-21T11:57:51.804557+00:00
-- url     : https://prove2.me/theorems/9312e42c-332f-443a-9077-198c51935103
-- title:
--   Proof of Theorem 2(i) — with costless entry, winner-take-all strictly maximizes the expected best submission
-- statement:
--   Fix $n\ge2$ and an ability distribution on $[0,1]$ with continuous, strictly positive density $f$ and CDF $F$. Let the participation cost be $c_p=0$, so every solver enters ($a_{\min}=0$) and the equilibrium performance of ability $a$ is
--   $$x^*(a)=\sum_{j=1}^{n-1}(r_j-r_{j+1})\int_0^a y\, f_{(n-j):(n-1)}(y)\,dy .$$
--   For every budget $B>0$ and every feasible allocation $r$ (nonnegative, weakly decreasing on ranks $1,\dots,n$, zero beyond rank $n$, total at most $B$) different from winner-take-all $(B,0,\dots,0)$,
--   $$\mathbb E\Big[\max_i x^*(A_i)\Big]\Big|_{r} \;<\; \mathbb E\Big[\max_i x^*(A_i)\Big]\Big|_{\text{WTA}} .$$
--   This is the first-term (expected best submission) claim of the proof of Theorem 2 specialised to costless entry, i.e. part (i) of Theorem 2: since the failure probability is zero when $c_p=0$, it makes winner-take-all the unique optimum.
-- source:
--   Stouras, Hutchison-Krupat & Chao, The Role of Participation in Innovation Contests, SSRN 2924224 (accepted version; Management Science 68(6) 2022, doi:10.1287/mnsc.2021.4111), p. 12, Theorem 2 (case c_p = 0); proof of Theorem 2, pp. 27–28 (first term maximized at WTA)

import Mathlib
import Definitions.Def_InnovContest_Rewards_Model

namespace InnovContest.Rewards

/-- Proof of Theorem 2(i), p. 28: with costless entry, winner-take-all strictly maximizes the
expected best submission. -/
theorem first_term_wta_zero (M : AbilityModel) (budget : ℝ) (hbudget : 0 < budget)
    (r : ℕ → ℝ) (hr : Feasible M.n budget r) (hne : r ≠ equalSplit budget 1) :
    bestExpected M r 0 < bestExpected M (equalSplit budget 1) 0 := by sorry

end InnovContest.Rewards
