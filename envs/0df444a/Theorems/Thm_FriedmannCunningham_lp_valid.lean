-- Prove2me | Theorems.Thm_FriedmannCunningham_lp_valid
-- name    : FriedmannCunningham.lp_valid
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-02T05:11:55.999619+00:00
-- url     : https://prove2.me/theorems/80c32de8-1102-45fc-8fe0-8f26f82bbf1a
-- title:
--   Policy bases and bounded polytope
-- statement:
--   For every n≥3 the graph-derived program has a bounded feasible set, and every Boolean policy selects a nonsingular feasible basis with strictly positive basic values.
-- source:
--   Avis and Friedmann (2017), §4.2 and §4.4 construction. https://oliverfriedmann.com/downloads/papers/cunningham_exponential_lower_bound.pdf

import Definitions.Def_friedmann_cunningham

set_option autoImplicit false

namespace FriedmannCunningham

/-- Construction validity needed by the §4.2 policy/BFS correspondence.
The graph-derived reward retains the aliases discussed in the source notes. -/
theorem lp_valid (n : ℕ) (hn : 3 ≤ n) :
    FriedmannSimplex.bounded (program n) ∧
    ∀ σ : Policy n,
      FriedmannSimplex.basicFeasible (program n) (policyBasis n hn σ) ∧
        ∀ i, 0 < FriedmannSimplex.basicValues (program n) (policyBasis n hn σ) i := by sorry

end FriedmannCunningham
