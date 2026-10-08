-- Prove2me | Theorems.Thm_HordijkKallenbergLP_Correspondence_theorem_6
-- name    : HordijkKallenbergLP.Correspondence.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:18.668346+00:00
-- url     : https://prove2.me/theorems/84c00d95-2c9d-498a-996d-bb2d432708b0
-- title:
--   Theorem 6 — least superharmonic gain
-- statement:
--   For a finite Markov decision process, let $\phi_i$ be the supremum, over all history-dependent randomized policies, of the liminf average reward starting at $i$. Then some $u$ makes $(\phi,u)$ superharmonic, and every superharmonic pair $(\widetilde\phi,\widetilde u)$ satisfies
--
--   $$\phi_i\le\widetilde\phi_i\quad\text{for every state }i.$$
--
--   This identifies the optimal gain vector as the componentwise least possible first component of a feasible primal pair.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 356, Theorem 6

import Mathlib
import Definitions.Def_HordijkKallenbergLP_Correspondence_Model

namespace HordijkKallenbergLP.Correspondence

open MarkovDecisionProcesses

/-- Hordijk and Kallenberg (1979), Theorem 6, p. 356.
The optimal average reward is the componentwise least first component of a
superharmonic pair. -/
theorem theorem_6 {S A : Type*} [Fintype S] [Fintype A] [Nonempty S]
    (M : StationaryMDP S A) :
    (∃ u : S → ℝ, HordijkKallenbergLP.SingleLP.Superharmonic M (optGainInf M) u) ∧
    (∀ φ u : S → ℝ, HordijkKallenbergLP.SingleLP.Superharmonic M φ u → ∀ i, optGainInf M i ≤ φ i) := by sorry

end HordijkKallenbergLP.Correspondence
