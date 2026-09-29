-- Prove2me | Theorems.Thm_MarkovMixing_gamblers_ruin
-- name    : MarkovMixing.gamblers_ruin
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T01:43:32.03629+00:00
-- url     : https://prove2.me/theorems/9ff4be64-77d7-4b77-b289-b0919f1c82ce
-- title:
--   Proposition 2.1 -- gambler's ruin
-- statement:
--   For the fair unit-bet gambler absorbed at $0$ and $n$, started from fortune $k\in\{0,\dots,n\}$: the probability of reaching $n$ before $0$ is $k/n$, and the expected absorption time is $k(n-k)$. Both quantities are expressed by tail/first-passage sums over trajectories of the explicit gambler's chain.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 2.1, Proposition 2.1, p. 21

import Definitions.Def_mm_classical

namespace MarkovMixing

/-- **Proposition 2.1** (LPW), gambler's ruin: for fair unit bets absorbed at
`0` and `n`, started from `k` the probability of reaching `n` before `0` is
`k/n`, and the expected absorption time is `k(n-k)`. -/
theorem gamblers_ruin (n : ℕ) (hn : 0 < n) (k : Fin (n + 1)) :
    hitBeforeProb (gamblersChain n) k (Fin.last n) 0 = (k.val : ℝ) / n ∧
    expSetHitTime (gamblersChain n) k {0, Fin.last n} =
      (k.val : ℝ) * ((n : ℝ) - (k.val : ℝ)) := by
  sorry

end MarkovMixing
