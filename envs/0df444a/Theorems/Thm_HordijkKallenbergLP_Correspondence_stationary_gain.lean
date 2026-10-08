-- Prove2me | Theorems.Thm_HordijkKallenbergLP_Correspondence_stationary_gain
-- name    : HordijkKallenbergLP.Correspondence.stationary_gain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:13:19.735056+00:00
-- url     : https://prove2.me/theorems/90c4d873-2cd6-4ae5-b92c-8399b38d00e6
-- title:
--   §3.3 — stationary gain from the Cesàro limit
-- statement:
--   Let $\pi$ be any stationary randomized policy of a finite Markov decision process, with transition matrix $P(\pi)$, one-step reward vector $r(\pi)$ and Cesàro limit matrix $P^*(\pi)$. Its liminf average reward is
--
--   $$\phi_i(\pi^\infty)=\bigl[P^*(\pi)r(\pi)\bigr]_i\quad\text{for every state }i.$$
--
--   This converts the policy's long-run performance into the matrix expression used by its representative. **Formalization Note** The other identities stated in the same paragraph of the paper belong to Blackwell's existing limit and deviation matrix results.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 359, §3.3

import Mathlib
import Definitions.Def_HordijkKallenbergLP_Correspondence_Representative

namespace HordijkKallenbergLP.Correspondence

open MarkovDecisionProcesses Matrix

/-- Hordijk and Kallenberg (1979), §3.3, p. 359, the final clause after
the limit and deviation matrix identities. -/
theorem stationary_gain {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] [DecidableEq A] [Nonempty S]
    (M : StationaryMDP S A) (π : RandomizedPolicy M) (i : S) :
    gainInf π.toHR i = (Pstar M π).mulVec (policyReward M π) i := by sorry

end HordijkKallenbergLP.Correspondence
