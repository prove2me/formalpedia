-- Prove2me | Theorems.Thm_OnlineStochMatching_SuggestedMatching_opt_bound
-- name    : OnlineStochMatching.SuggestedMatching.opt_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T22:03:41.974761+00:00
-- url     : https://prove2.me/theorems/cc802405-ee4a-451c-9da1-057a31b2d73c
-- title:
--   §4.1 Bounding OPT — concentration of the hindsight optimum
-- statement:
--   For any maximum integral expected-instance matching $M$, let $A^*$ be its covered advertisers. For every $\varepsilon>0$, there are constants $\delta>0$ and $N$ independent of the instance and $M$ such that, whenever $n\ge N$,
--
--   $$\Pr\!\left[\mathrm{OPT}\le |A^*|+\varepsilon n\right]\ge1-e^{-\delta n}.$$
--
--   The random optimum is the maximum matching of the arrival-by-arrival realization graph. The paper writes the failure probability as $e^{-\Omega(n)}$; the formal statement gives its uniform quantifiers.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, p. 6, §4.1, Bounding OPT

import Definitions.Def_OnlineStochMatching_SuggestedMatching_Algorithm
import Definitions.Def_OnlineStochMatching_SuggestedMatching_Cut

namespace OnlineStochMatching.SuggestedMatching

/-- Section 4.1's high-probability bound on the hindsight optimum. -/
theorem opt_bound :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ (A I : Type) [Fintype A] [Fintype I]
        (inst : Instance A I) (hn : N ≤ inst.n)
        (M : Finset (A × I)) (hM : IsMaxBMatching inst M),
        runProbability inst (fun ω =>
          (optimum inst ω : ℝ) ≤ (coveredAds M).card + ε * (inst.n : ℝ)) ≥
          1 - Real.exp (-δ * (inst.n : ℝ)) := by sorry

end OnlineStochMatching.SuggestedMatching
