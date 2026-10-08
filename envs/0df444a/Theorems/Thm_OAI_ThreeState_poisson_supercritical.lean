-- Prove2me | Theorems.Thm_OAI_ThreeState_poisson_supercritical
-- name    : OAI.ThreeState.poisson_supercritical
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:31.722914+00:00
-- url     : https://prove2.me/theorems/cd9226f6-5a3c-418a-88ea-1efa46b8828f
-- statement:
--   The theorem states that, for a three-state spin model with spins in {0,1,2}, take a real d > 1 and a parameter λ that is admissible, meaning -1/2 ≤ λ ≤ 1. Each spin is passed through a noisy channel that keeps it with probability (1+2λ)/3 and changes it to each other particular spin with probability (1-λ)/3. Observations are built recursively: at depth 0 one sees the spin itself, and at depth n+1 the root draws a Poisson(d) number k of children, passes each of k independent child spins (each obtained from the root spin through the channel) through the depth-n observation procedure, and records the resulting unordered multiset of k depth-n observations. The advantage at depth n is the expected total-variation distance between the posterior on the root spin, given the observation under a uniform prior, and the uniform distribution on the three spins, namely the average over observations y of half the sum over spins i of |posterior(i | y) - 1/3|. Assuming the supercritical condition 1 < d·λ², the theorem concludes that this Poisson advantage sequence reconstructs, meaning it converges as n tends to infinity to some limit L that is strictly positive. The statement is admitted without proof in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ThreeStateSupercritical.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ThreeStateSupercritical.lean; bytes 3380..3554
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_ThreeStateSupercritical

namespace OAI

namespace ThreeState

theorem poisson_supercritical (d : ℝ) (hd : 1 < d) (lam : ℝ) (h : Admissible lam)
    (hcrit : 1 < d * lam ^ 2) : Reconstructs (poissonAdvantage d hd lam h) := by
  sorry

end ThreeState
end OAI
