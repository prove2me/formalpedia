-- Prove2me | Theorems.Thm_FriedmannCunningham_simplex_lower_bound
-- name    : FriedmannCunningham.simplex_lower_bound
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-02T05:13:12.969336+00:00
-- url     : https://prove2.me/theorems/5ab9a8e2-e11c-4a30-a521-01a4143ffc5b
-- title:
--   Theorem 7 — simplex lower bound
-- statement:
--   For every n≥3 the graph-derived linear program has a complete Cunningham simplex execution from the specified basis and order (1), requiring at least 2^n pivots and strictly increasing the objective on every pivot.
-- source:
--   Avis and Friedmann (2017), Theorem 7, §4.4 interpreted via Figure 7 and §§4.2–4.3. https://oliverfriedmann.com/downloads/papers/cunningham_exponential_lower_bound.pdf

import Definitions.Def_friedmann_cunningham

set_option autoImplicit false

namespace FriedmannCunningham

/-- Theorem 7: the graph-derived LP, the prescribed order and initial basis,
at least 2^n pivots, and strict objective increase on every pivot. -/
theorem simplex_lower_bound (n : ℕ) (hn : 3 ≤ n) :
    ∃ (T : ℕ) (s : ℕ → FriedmannSimplex.State (rows n) (cols n)),
      s 0 = initialState n hn ∧
      FriedmannSimplex.cunninghamRun (program n) (order n) s T ∧
      2 ^ n ≤ T ∧
      ∀ t, t < T →
        FriedmannSimplex.basicObjective (program n) (s t).basis <
          FriedmannSimplex.basicObjective (program n) (s (t + 1)).basis := by sorry

end FriedmannCunningham
