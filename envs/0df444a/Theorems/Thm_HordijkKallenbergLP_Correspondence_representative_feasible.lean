-- Prove2me | Theorems.Thm_HordijkKallenbergLP_Correspondence_representative_feasible
-- name    : HordijkKallenbergLP.Correspondence.representative_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:15:18.391536+00:00
-- url     : https://prove2.me/theorems/74626729-08e8-418e-81a8-b1510477138f
-- title:
--   §3.3 — representative satisfies the dual LP
-- statement:
--   Let $\beta_i>0$ and $\sum_i\beta_i=1$. For every stationary randomized policy $\pi$, form the representative $(x(\pi),y(\pi))$ by equation (6), including the class-wise choice of $\gamma$. Then
--
--   $$(x(\pi),y(\pi))\text{ satisfies the dual constraints (3)–(5).}$$
--
--   Thus each stationary policy determines a feasible dual point, even when its Markov chain has several recurrent classes. The dual coordinates are indexed only by admissible state-action pairs.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, pp. 359–360, §3.3, equation (6) and properties 1–4

import Mathlib
import Definitions.Def_HordijkKallenbergLP_Correspondence_Representative

namespace HordijkKallenbergLP.Correspondence

open MarkovDecisionProcesses

/-- Hordijk and Kallenberg (1979), §3.3, pp. 359–360, equation (6) and
properties 1–4: the representative is dual feasible. -/
theorem representative_feasible {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] [DecidableEq A] [Nonempty S]
    (M : StationaryMDP S A) (β : S → ℝ)
    (hβpos : ∀ i, 0 < β i) (hβsum : ∑ i, β i = 1)
    (π : RandomizedPolicy M) :
    DualFeasible M β (representativeX M β π) (representativeY M β π) := by sorry

end HordijkKallenbergLP.Correspondence
