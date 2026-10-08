-- Prove2me | Theorems.Thm_OnlineStochMatching_SuggestedMatching_bounding_alg
-- name    : OnlineStochMatching.SuggestedMatching.bounding_alg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T22:03:01.374986+00:00
-- url     : https://prove2.me/theorems/9c26890b-adde-4887-afa7-746833e8f3e3
-- title:
--   §4.1 Bounding ALG — assignments from the selected flow
-- statement:
--   Let $A^*$ be the advertisers covered by any maximum integral expected-instance matching $M$. For every $\varepsilon>0$, there are constants $\delta>0$ and $N$ independent of the instance, $M$, and its labelling such that, whenever $n\ge N$,
--
--   $$\Pr\!\left[\mathrm{ALG}\ge(1-e^{-1})|A^*|-\varepsilon n\right]\ge1-e^{-\delta n}.$$
--
--   This is the assignment side of Theorem 4's analysis. The paper writes the failure probability as $e^{-\Omega(n)}$; the constants are quantified before the instance to make that uniform claim explicit.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, p. 5, §4.1, Bounding ALG

import Definitions.Def_OnlineStochMatching_SuggestedMatching_Algorithm

namespace OnlineStochMatching.SuggestedMatching

/-- Section 4.1, "Bounding ALG": the paper's exponential concentration claim. -/
theorem bounding_alg :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ (A I : Type) [Fintype A] [Fintype I]
        (inst : Instance A I) (hn : N ≤ inst.n)
        (M : Finset (A × I)) (hM : IsMaxBMatching inst M)
        (label : inst.Copy → Option A) (hlabel : IsLabelling inst M label),
        runProbability inst (fun ω =>
          (1 - Real.exp (-1)) * (coveredAds M).card - ε * (inst.n : ℝ) ≤
            (algorithm inst label ω : ℝ)) ≥
          1 - Real.exp (-δ * (inst.n : ℝ)) := by sorry

end OnlineStochMatching.SuggestedMatching
