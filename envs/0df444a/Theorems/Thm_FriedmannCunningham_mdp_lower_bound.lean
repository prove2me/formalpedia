-- Prove2me | Theorems.Thm_FriedmannCunningham_mdp_lower_bound
-- name    : FriedmannCunningham.mdp_lower_bound
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-02T05:12:29.099347+00:00
-- url     : https://prove2.me/theorems/d514b4de-fa8b-407f-b865-8cbd4211383b
-- title:
--   Theorem 6 — policy-iteration lower bound
-- statement:
--   For every n≥3 the graph-derived collapsed decision process admits a complete policy-iteration run from the explicit Sections 2.3/4.4 policy and cyclic order with at least 2^n switches.
-- source:
--   Avis and Friedmann (2017), Theorem 6, §3.3. https://oliverfriedmann.com/downloads/papers/cunningham_exponential_lower_bound.pdf Uses the explicit counter start of Sections 2.3 and 4.4; the transfer from Theorem 4 supplies the bound, rather than subtracting the shorthand start’s first switch from Theorem 6.

import Definitions.Def_friedmann_cunningham

set_option autoImplicit false

namespace FriedmannCunningham

/-- Theorem 6, expressed on the equivalent decision-state MDP. -/
theorem mdp_lower_bound (n : ℕ) (hn : 3 ≤ n) :
    ∃ (T : ℕ) (s : ℕ → MDPState n), mdpRun n hn s T ∧ 2 ^ n ≤ T := by sorry

end FriedmannCunningham
