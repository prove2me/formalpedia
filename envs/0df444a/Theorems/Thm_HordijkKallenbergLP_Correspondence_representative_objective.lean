-- Prove2me | Theorems.Thm_HordijkKallenbergLP_Correspondence_representative_objective
-- name    : HordijkKallenbergLP.Correspondence.representative_objective
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:14:09.167988+00:00
-- url     : https://prove2.me/theorems/8636efea-5baf-4c53-9455-86a20ba86ae9
-- title:
--   Theorem 8(a) proof — objective of the representative
-- statement:
--   For any positive normalized state weights $\beta$ and stationary randomized policy $\pi$, the dual objective at its representative equals the $\beta$-weighted average reward of the policy:
--
--   $$\sum_i\sum_{a\in A(i)}r_{ia}x_{ia}(\pi)=\sum_i\beta_i\phi_i(\pi^\infty).$$
--
--   This is the objective identity used to compare an optimal policy with the primal optimum in Theorem 8(a). It makes no optimality assumption on $\pi$.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 360, proof of Theorem 8(a)

import Mathlib
import Definitions.Def_HordijkKallenbergLP_Correspondence_Representative

namespace HordijkKallenbergLP.Correspondence

open MarkovDecisionProcesses

/-- Hordijk and Kallenberg (1979), proof of Theorem 8(a), p. 360:
the representative's dual objective is the β-weighted gain of its policy. -/
theorem representative_objective {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] [DecidableEq A] [Nonempty S]
    (M : StationaryMDP S A) (β : S → ℝ)
    (hβpos : ∀ i, 0 < β i) (hβsum : ∑ i, β i = 1)
    (π : RandomizedPolicy M) :
    dualObjective M (representativeX M β π) =
      ∑ i, β i * gainInf π.toHR i := by sorry

end HordijkKallenbergLP.Correspondence
