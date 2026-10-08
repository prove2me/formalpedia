-- Prove2me | Theorems.Thm_OnlineStochMatching_SuggestedMatching_tightness
-- name    : OnlineStochMatching.SuggestedMatching.tightness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T22:03:17.299003+00:00
-- url     : https://prove2.me/theorems/9926fae1-414b-4f41-bb94-c8239db9d043
-- title:
--   §4.1 Tightness — complete bipartite family
-- statement:
--   For every $n\ge1$, take the complete bipartite graph with $n$ advertisers and $n$ impression types, each with $e_i=1$. For every maximum expected-instance matching and every valid labelling, the hindsight optimum is $n$ in every scenario, while
--
--   $$\mathbb E[\mathrm{ALG}]=n\left(1-\left(1-\frac1n\right)^n\right).$$
--
--   This is the exact finite-$n$ expectation underlying the paper's statement that the $1-1/e$ factor is tight even in expectation. Each maximum matching is perfect in this family.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, p. 6, §4.1, Tightness of the Analysis

import Definitions.Def_OnlineStochMatching_SuggestedMatching_Algorithm

namespace OnlineStochMatching.SuggestedMatching

/-- The exact expectation and optimum for the complete-graph family in Section 4.1. -/
theorem tightness :
    ∀ (n : ℕ) (hn : 0 < n),
      let inst := completeInstance n hn
      ∀ (M : Finset (Fin n × Fin n)) (hM : IsMaxBMatching inst M)
        (label : inst.Copy → Option (Fin n)) (hlabel : IsLabelling inst M label),
        (∀ ω : Fin inst.n → inst.Copy, optimum inst ω = n) ∧
          expectedAlgorithm inst label =
            (n : ℝ) * (1 - (1 - 1 / (n : ℝ)) ^ n) := by sorry

end OnlineStochMatching.SuggestedMatching
